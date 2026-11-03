/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearPointwise
public import WaveTurbulence.Foundations.WeylSums.RefinedMomentPowers
public import WaveTurbulence.Foundations.WeylSums.WindowScaling

/-! # The bilinear minor-arc integral before substituting the time scale -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- TARGET Lemma 5.3 at an arbitrary upper time `B`: the window factor is
`(B/(4L²))^(d-1-ε)`, with any arbitrarily small `ε>0`. All real spatial
centers and linear frequencies are uniform. -/
theorem exists_bilinear_minor_integral_bound (d : ℕ) (hd : 3 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hεd : ε < (d : ℝ)-2) :
    ∃ C : ℝ, 0 < C ∧ ∀ L B : ℝ, 2 ≤ L → 0 < B → ∀ a b ξ ζ : Mom d,
      IntegrableOn (fun s : ℝ => ‖bilinearLatticeSum L s a b ξ ζ‖)
        {s : ℝ | L ≤ |s| ∧ |s| ≤ B} ∧
      (∫ s : ℝ in {s : ℝ | L ≤ |s| ∧ |s| ≤ B}, ‖bilinearLatticeSum L s a b ξ ζ‖) ≤
        C * L^(2*(d : ℝ)) * (B/(4*L^2))^((d : ℝ)-1-ε) := by
  let p : ℝ := 2*(d : ℝ)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 4 < p := by dsimp [p]; linarith only [hdR]
  have hεp : ε < p/2-2 := by dsimp [p]; linarith only [hεd]
  obtain ⟨C₀,hC₀,hpoint⟩ := exists_bilinearLatticeSum_pointwise_bound
  obtain ⟨C₁,hC₁,hint⟩ := exists_weylSupremum_refined_moment p ε hp hε hεp
  let C := C₀^d * C₁ * (4*(12 : ℝ)^(p-2))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro L B hL hB a b ξ ζ
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  let M := 12*L
  let c := 4*L^2
  let T := B/c
  have hM : 2 ≤ M := by dsimp [M]; linarith only [hL]
  have hMp : 0 < M := by dsimp [M]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hT : 0 < T := div_pos hB hc
  let f : ℝ → ℝ := fun t => weylSupremum M t ^ p
  obtain ⟨hi,hi_bound⟩ := hint M T hM hT
  have hf (t : ℝ) : 0 ≤ f t := Real.rpow_nonneg (weylSupremum_nonneg hMp t) _
  have hA : 1/M ≤ L/c := by
    apply (div_le_div_iff₀ hMp hc).mpr
    dsimp [M,c]
    nlinarith only [sq_nonneg L]
  have hi_small : IntegrableOn f {t : ℝ | L/c ≤ |t| ∧ |t| ≤ B/c} :=
    hi.mono_set (fun t ht => ⟨hA.trans ht.1, ht.2⟩)
  have hi_comp := integrableOn_abs_window_div L B hc hi_small
  have hpt (s : ℝ) : ‖bilinearLatticeSum L s a b ξ ζ‖ ≤ C₀^d * f (s/c) := by
    have hh := hpoint d L hL1 s a b ξ ζ
    have hpcast : p = ((2*d : ℕ) : ℝ) := by dsimp [p]; push_cast; ring
    simpa only [f, M, c, hpcast, Real.rpow_natCast] using hh
  have hfm : AEStronglyMeasurable (fun s : ℝ => ‖bilinearLatticeSum L s a b ξ ζ‖)
      (volume.restrict {s : ℝ | L ≤ |s| ∧ |s| ≤ B}) :=
    (continuous_bilinearLatticeSum hLp a b ξ ζ).norm.aestronglyMeasurable
  have hi_sum : IntegrableOn (fun s : ℝ => ‖bilinearLatticeSum L s a b ξ ζ‖)
      {s : ℝ | L ≤ |s| ∧ |s| ≤ B} := by
    apply (hi_comp.const_mul (C₀^d)).mono' hfm
    filter_upwards [] with s
    rw [norm_norm]
    exact hpt s
  refine ⟨hi_sum, ?_⟩
  have hscale : c * M^(p-2) = (4*(12 : ℝ)^(p-2)) * L^p := by
    dsimp [c,M]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) hLp.le,
      Real.rpow_sub hLp, Real.rpow_two]
    field_simp [hLp.ne']
  calc
    _ ≤ ∫ s : ℝ in {s : ℝ | L ≤ |s| ∧ |s| ≤ B}, C₀^d*f (s/c) :=
      integral_mono_ae hi_sum (hi_comp.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = C₀^d * ∫ s : ℝ in {s : ℝ | L ≤ |s| ∧ |s| ≤ B}, f (s/c) := integral_const_mul _ _
    _ ≤ C₀^d * (c * ∫ t : ℝ in {t : ℝ | 1/M ≤ |t| ∧ |t| ≤ T}, f t) :=
      mul_le_mul_of_nonneg_left (integral_abs_window_div_le hf L B (1/M) T hc hi hA le_rfl)
        (pow_nonneg hC₀.le d)
    _ ≤ C₀^d * (c * (C₁*M^(p-2)*T^(p/2-1-ε))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi_bound hc.le) (pow_nonneg hC₀.le d)
    _ = C * L^p * T^(p/2-1-ε) := by
      calc
        _ = (C₀^d*C₁) * (c*M^(p-2)) * T^(p/2-1-ε) := by ring
        _ = _ := by rw [hscale]; dsimp [C]; ring
    _ = _ := by
      dsimp [p,T,c]
      congr 2
      ring

end WaveTurbulence.WeylSums
