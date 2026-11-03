/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicChainPointwise
public import WaveTurbulence.Foundations.WeylSums.CubicChainWeylIntegral

/-! # The integrated cubic-chain lattice sum -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- The unnormalized physical-time estimate before the upper time scale
is substituted. It is uniform in all six real vector parameters. -/
theorem exists_cubicChain_integral_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L B : ℝ, 2 ≤ L → 0 < B → B ≤ L^2 →
      ∀ a b c ξ ζ ω : Mom d,
      IntegrableOn (fun ts : ℝ × ℝ => ‖cubicLatticeSum L ts.1 ts.2 false a b c ξ ζ ω‖)
        (timeSquareWindow L B) ∧
      (∫ ts : ℝ × ℝ in timeSquareWindow L B, ‖cubicLatticeSum L ts.1 ts.2 false a b c ξ ζ ω‖) ≤
        C*L^(3*(d : ℝ))*(B/(4*L^2))^((2 : ℝ)/3) := by
  obtain ⟨C₀,hC₀,hpoint⟩ := exists_cubicChain_pointwise_bound
  obtain ⟨C₁,hC₁,hint⟩ := exists_cubicChain_weyl_integral_bound d hd
  let r : ℝ := 3*(d : ℝ)-4
  let C := C₀^d*C₁*(16*(20 : ℝ)^r)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro L B hL hB hBL a b c ξ ζ ω
  have hLp : 0 < L := by linarith
  let J := 4*L^2
  let M := 20*L
  let T := B/J
  let A := L/J
  have hJ : 0 < J := by dsimp [J]; positivity
  have hM : 2 ≤ M := by dsimp [M]; linarith
  have hMp : 0 < M := by dsimp [M]; positivity
  have hT : 0 < T := div_pos hB hJ
  have hTsmall : T ≤ 1/4 := by
    rw [show T = B/(4*L^2) from rfl, div_le_iff₀ hJ]
    linarith only [hBL]
  have hA : 1/M ≤ A := by
    apply (div_le_div_iff₀ hMp hJ).mpr
    dsimp [M,J]
    nlinarith only [sq_nonneg L]
  let f := fun xy : ℝ × ℝ => weylSupremum M xy.1^d*weylSupremum M xy.2^d*
    weylSupremum M (xy.1+xy.2)^d
  obtain ⟨hi,hb⟩ := hint M A T hM hA hT.le hTsmall
  have hic := integrableOn_timeSquareWindow_div L B hJ hi
  have hpt (ts : ℝ × ℝ) : ‖cubicLatticeSum L ts.1 ts.2 false a b c ξ ζ ω‖ ≤
      C₀^d*f (ts.1/J,ts.2/J) := by
    calc
      _ ≤ C₀^d*weylSupremum M ((ts.1+ts.2)/J)^d*
          weylSupremum M (ts.1/J)^d*weylSupremum M (ts.2/J)^d :=
        hpoint d L (by linarith) ts.1 ts.2 a b c ξ ζ ω
      _ = _ := by dsimp [f]; rw [← add_div]; ring
  have hsource : IntegrableOn (fun ts : ℝ × ℝ => ‖cubicLatticeSum L ts.1 ts.2 false a b c ξ ζ ω‖)
      (timeSquareWindow L B) := by
    apply (hic.const_mul (C₀^d)).mono'
      (continuous_cubicLatticeSum hLp false a b c ξ ζ ω).norm.aestronglyMeasurable
    filter_upwards [] with ts
    rw [norm_norm]
    exact hpt ts
  refine ⟨hsource,?_⟩
  have hscale : J^2*M^r = (16*(20 : ℝ)^r)*L^(3*(d : ℝ)) := by
    dsimp [J,M,r]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 20) hLp.le,
      Real.rpow_sub hLp, show L^(4 : ℝ) = L^4 by norm_cast]
    field_simp [hLp.ne']
    ring
  calc
    _ ≤ ∫ ts in timeSquareWindow L B, C₀^d*f (ts.1/J,ts.2/J) :=
      integral_mono_ae hsource (hic.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = C₀^d*(J^2*∫ xy in timeSquareWindow A T, f xy) := by
      rw [integral_const_mul,integral_timeSquareWindow_div f L B hJ]
    _ ≤ C₀^d*(J^2*(C₁*M^r*T^((2 : ℝ)/3))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (sq_nonneg J)) (pow_nonneg hC₀.le d)
    _ = C*L^(3*(d : ℝ))*T^((2 : ℝ)/3) := by
      calc
        _ = (C₀^d*C₁)*(J^2*M^r)*T^((2 : ℝ)/3) := by ring
        _ = _ := by rw [hscale]; dsimp [C]; ring

end WaveTurbulence.WeylSums
