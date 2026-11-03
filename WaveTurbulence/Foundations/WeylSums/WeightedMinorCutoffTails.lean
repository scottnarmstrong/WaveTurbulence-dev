/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeightedMinorCutoff
public import WaveTurbulence.Foundations.WeylSums.PolynomialTimeWeight

/-! # Weighted infinite-time minor-arc bounds -/

public section
open MeasureTheory
open scoped ContDiff
namespace WaveTurbulence.WeylSums

/-- The full weighted minor-arc integral before substituting `B=δL^(2γ)`.
The constant is uniform in the decay power `P≥2d`, all centers, the amplitude,
and the cutoff width. -/
theorem exists_weighted_bilinear_tail_bound_of_cutoff (d : ℕ) (hd : 3 ≤ d)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (ε : ℝ) (hε : 0 < ε) (hεd : ε < (d : ℝ)-2) :
    ∃ C : ℝ, 0 < C ∧ ∀ L width B P : ℝ, 2 ≤ L → 1 ≤ width → 0 < B → 2*(d : ℝ) ≤ P →
      ∀ (Φ : ℝ → Mom d → Mom d → ℂ),
      (∀ x y, Measurable (fun s => Φ s x y)) →
      (∀ s, ContDiff ℝ (10*d) (packedBilinearAmplitude (Φ s))) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ s, ∀ j ≤ 10*d, ∀ x, ‖iteratedFDeriv ℝ j (packedBilinearAmplitude (Φ s)) x‖ ≤ D) →
      ∀ a b ξ ζ : Mom d,
      IntegrableOn (fun s : ℝ => japaneseTimeWeight B P s*‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖)
        {s : ℝ | c₀*L ≤ |s|} ∧
      (∫ s : ℝ in {s : ℝ | c₀*L ≤ |s|}, japaneseTimeWeight B P s*‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖) ≤
        C * D * width^(4*d) * L^(2*(d : ℝ)) * (B/(4*L^2))^((d : ℝ)-1-ε) := by
  let r := (d : ℝ)-1-ε
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 < r := by dsimp [r]; linarith
  have hrk : r < 2*(d : ℝ) := by dsimp [r]; linarith
  let H := 1+(2 : ℝ)^r/(1-(2 : ℝ)^(r-2*(d : ℝ)))
  have hratio : (2 : ℝ)^(r-2*(d : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨C,hC,hint⟩ := exists_weighted_bilinear_minor_integral_bound_of_cutoff d hd c₀ hc₀ ε hε hεd
  refine ⟨C*H,mul_pos hC hH,?_⟩
  intro L width B P hL hw hB hP Φ htime hΦ D hD hderiv a b ξ ζ
  have hLp : 0 < L := by linarith
  have hc : 0 < 4*L^2 := by positivity
  let μ := volume.restrict {s : ℝ | c₀*L ≤ |s|}
  let g := fun s : ℝ => ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖
  let K := C*D*width^(4*d)*L^(2*(d : ℝ))*(1/(4*L^2))^r
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hrestrict (U : ℝ) : μ.restrict {s : ℝ | |s| ≤ U} =
      volume.restrict {s : ℝ | c₀*L ≤ |s| ∧ |s| ≤ U} := by
    dsimp only [μ]
    rw [Measure.restrict_restrict (by measurability)]
    congr 1
    ext s
    exact and_comm
  have hi (U : ℝ) (hU : 0 < U) : IntegrableOn g {s : ℝ | |s| ≤ U} μ := by
    have hh := (hint L width U hL hw hU Φ htime hΦ D hD hderiv a b ξ ζ).1
    simpa only [IntegrableOn, hrestrict, g] using hh
  have hb (U : ℝ) (hU : 0 < U) : (∫ s in {s : ℝ | |s| ≤ U}, g s ∂μ) ≤ K*U^r := by
    rw [hrestrict]
    have hh := (hint L width U hL hw hU Φ htime hΦ D hD hderiv a b ξ ζ).2
    have heq : U/(4*L^2) = (1/(4*L^2))*U := by ring
    simpa only [K,g,r,heq,Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1/(4*L^2)) hU.le,mul_assoc] using hh
  have hh := japanese_weighted_integral_bound μ g (fun s => norm_nonneg _) B K r (d : ℝ) P
    hB hK (by positivity) hrk hP hi hb
  refine ⟨hh.1,?_⟩
  calc
    _ ≤ K*B^r*H := hh.2
    _ = _ := by
      dsimp [K]
      rw [show B/(4*L^2) = (1/(4*L^2))*B by ring,
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1/(4*L^2)) hB.le]
      ring

end WaveTurbulence.WeylSums
