/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ApproximationL1Moments
public import WaveTurbulence.Foundations.XChain.InductParameters
/-! The retained fixedpoint bounds supply all l1 moments internally on the very same new event. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
open scoped ENNReal

theorem fixedpoint_bounds_memLp_l1 (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Set Ω) (hF : MeasurableSet F)
    (p : ℕ) (hp : p < P.D) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (old A : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (t : ℝ)
    (hAt : ∀ n, Measurable (fun ω => A ω t n))
    (htr : ∀ ω ∈ F, ∀ n,
      ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (old ω p) t n‖ ≤
        jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
          Real.exp (3 * P.N (p + 1)))
    (herr : ∀ ω ∈ F, ∀ n,
      ‖A ω t n - aTr P.L P.γ P.δ p (P.N (p + 1)) (old ω p) t n‖ ≤
        jbr (latticePoint P.L n) ^ (-(5 / 4 * P.Lambda (p + 1) : ℝ)) *
          Real.exp (-(10 * P.N (p + 1) : ℝ))) (q : ℝ≥0∞) :
    MemLp (fun ω => ∑' n, ‖A ω t n‖) q (μ.restrict F) := by
  apply memLp_l1_of_two_spatial_bounds (μ.restrict F) P.L
    (3 / 2 * P.Lambda (p + 1)) (5 / 4 * P.Lambda (p + 1))
    (Real.exp (3 * P.N (p + 1))) (Real.exp (-(10 * P.N (p + 1) : ℝ)))
    hL (fixedpoint_weight_ge P hd hp) (fixedpoint_weight_le_tree_weight P p)
    (Real.exp_pos _).le (Real.exp_pos _).le (fun ω n => A ω t n)
    (fun ω n => aTr P.L P.γ P.δ p (P.N (p + 1)) (old ω p) t n) hAt _ _ q
  · filter_upwards [ae_restrict_mem hF] with ω hω
    exact htr ω hω
  · filter_upwards [ae_restrict_mem hF] with ω hω
    exact herr ω hω

end WaveTurbulence.Induct
