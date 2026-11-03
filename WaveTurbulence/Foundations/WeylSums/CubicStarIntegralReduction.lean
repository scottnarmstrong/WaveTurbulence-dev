/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicStarPointwise
public import WaveTurbulence.Foundations.WeylSums.CubicChainPointwise
public import WaveTurbulence.Foundations.WeylSums.TimeSquareScaling

/-! # Exact physical-time consumption of the shared-vertex majorant -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- The physical lattice integral is bounded by the normalized Weyl
minimum after the exact two-time change of variables. The integrability
premise is supplied by the proved product-moment bounds. -/
theorem exists_cubicStar_integral_reduction :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ L B : ℝ, 1 ≤ L →
      IntegrableOn (fun xy : ℝ × ℝ => min (normalizedWeyl (12*L) xy.1^d) (normalizedWeyl (12*L) xy.2^d))
        (timeSquareWindow (L/(4*L^2)) (B/(4*L^2))) →
      ∀ a b c ξ ζ ω : Mom d,
      IntegrableOn (fun ts : ℝ × ℝ => ‖cubicLatticeSum L ts.1 ts.2 true a b c ξ ζ ω‖)
        (timeSquareWindow L B) ∧
      (∫ ts : ℝ × ℝ in timeSquareWindow L B, ‖cubicLatticeSum L ts.1 ts.2 true a b c ξ ζ ω‖) ≤
        C^d*L^(2*d)*(4*L^2)^2 *
        (∫ xy : ℝ × ℝ in timeSquareWindow (L/(4*L^2)) (B/(4*L^2)),
          min (normalizedWeyl (12*L) xy.1^d) (normalizedWeyl (12*L) xy.2^d)) := by
  obtain ⟨C,hC,hpoint⟩ := exists_cubicStar_pointwise_bound
  refine ⟨C,hC,?_⟩
  intro d L B hL hi a b c ξ ζ ω
  have hLp : 0 < L := by linarith
  have hJ : 0 < 4*L^2 := by positivity
  let f := fun xy : ℝ × ℝ => min (normalizedWeyl (12*L) xy.1^d) (normalizedWeyl (12*L) xy.2^d)
  have hic := integrableOn_timeSquareWindow_div L B hJ hi
  have hpt (ts : ℝ × ℝ) : ‖cubicLatticeSum L ts.1 ts.2 true a b c ξ ζ ω‖ ≤
      C^d*L^(2*d)*f (ts.1/(4*L^2),ts.2/(4*L^2)) :=
    hpoint d L hL ts.1 ts.2 a b c ξ ζ ω
  have hsource : IntegrableOn (fun ts : ℝ × ℝ => ‖cubicLatticeSum L ts.1 ts.2 true a b c ξ ζ ω‖)
      (timeSquareWindow L B) := by
    apply (hic.const_mul (C^d*L^(2*d))).mono'
      (continuous_cubicLatticeSum hLp true a b c ξ ζ ω).norm.aestronglyMeasurable
    filter_upwards [] with ts
    rw [norm_norm]
    exact hpt ts
  refine ⟨hsource,?_⟩
  calc
    _ ≤ ∫ ts in timeSquareWindow L B, C^d*L^(2*d)*f (ts.1/(4*L^2),ts.2/(4*L^2)) :=
      integral_mono_ae hsource (hic.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = _ := by rw [integral_const_mul,integral_timeSquareWindow_div f L B hJ]; ring

end WaveTurbulence.WeylSums
