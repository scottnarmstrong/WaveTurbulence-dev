/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeightedBilinearTails
public import WaveTurbulence.Foundations.WeylSums.CoordinateDerivativeBounds
public import WaveTurbulence.Foundations.WeylSums.MinorArcExponents

/-!
# DH23 Lemma 6.6(2), with normalized lower time cutoff

The lower support convention here is `L≤|s|`. The decay condition is the
explicit sufficient condition `P≥2d`; the source's standing smallness of `η`
and `P>η⁻²` imply this. Coordinate derivative bounds are imposed only through
total order `10d`, a subset of the source's separate `x,y` orders through `10d`.
The width estimate holds for every `width≥1`.
-/

public section
open MeasureTheory Set
open scoped ContDiff
namespace WaveTurbulence.WeylSums

/-- DH23 minor-arc estimate with all coordinate, amplitude and time weights
explicit. The constant is independent of `δ`, `P`, `D`, width and centers. -/
theorem dh23_minor2_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ L width δ P : ℝ, 2 ≤ L → 1 ≤ width →
      δ ∈ Ioc (0 : ℝ) 1 → 2*(d : ℝ) ≤ P →
      ∀ (Φ : ℝ → Mom d → Mom d → ℂ),
      (∀ x y, Measurable (fun s => Φ s x y)) →
      (∀ s, ContDiff ℝ (10*d) (packedBilinearAmplitude (Φ s))) →
      (∀ s, |s| < L → ∀ x y, Φ s x y = 0) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ s, CoordinateDerivativeBound (10*d) (packedBilinearAmplitude (Φ s)) D) →
      ∀ a b ξ ζ : Mom d,
      Integrable (fun s => japaneseTimeWeight (δ*L^(2*γ)) P s*
        ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖) ∧
      (∫ s, japaneseTimeWeight (δ*L^(2*γ)) P s*‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖) ≤
        C*D*width^(4*d)*L^(2*(d : ℝ)-2*((d : ℝ)-1)*(1-γ)+η) := by
  obtain ⟨ε,hε,hεd,hεη⟩ := exists_minor_arc_loss d hd hη
  obtain ⟨C,hC,hb⟩ := exists_weighted_bilinear_tail_bound d hd ε hε hεd
  let J : ℝ := (Fintype.card (Fin d × Fin 2)+1 : ℝ)^(10*d)
  let r : ℝ := (d : ℝ)-1-ε
  have hr : 0 < r := by dsimp [r]; linarith
  let A := C*J*(1/4 : ℝ)^r
  have hJ : 0 < J := by dsimp [J]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro L width δ P hL hw hδ hP Φ htime hΦ hsupp D hD hcoord a b ξ ζ
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hB : 0 < δ*L^(2*γ) := mul_pos hδ.1 (Real.rpow_pos_of_pos hLp _)
  have hderiv (s : ℝ) (j : ℕ) (hj : j ≤ 10*d) (x : EuclideanSpace ℝ (Fin d × Fin 2)) :
      ‖iteratedFDeriv ℝ j (packedBilinearAmplitude (Φ s)) x‖ ≤ J*D :=
    (hcoord s).operator_bound hD j hj x
  have hh := hb L width (δ*L^(2*γ)) P hL hw hB hP Φ htime hΦ (J*D)
    (mul_nonneg hJ.le hD) hderiv a b ξ ζ
  let f := fun s : ℝ => japaneseTimeWeight (δ*L^(2*γ)) P s*
    ‖weightedBilinearLatticeSum Φ L width s a b ξ ζ‖
  have heq : {s : ℝ | L ≤ |s|}.indicator f = f := by
    funext s
    by_cases hs : L ≤ |s|
    · simp [hs]
    · have hz : weightedBilinearLatticeSum Φ L width s a b ξ ζ = 0 := by
        simp [weightedBilinearLatticeSum, hsupp s (lt_of_not_ge hs)]
      simp [hs,f,hz]
  have hfi : Integrable f := by
    rw [← heq]
    exact (integrable_indicator_iff (by measurability)).mpr hh.1
  refine ⟨hfi,?_⟩
  have hwhole : (∫ s, f s) = ∫ s in {s : ℝ | L ≤ |s|}, f s := by
    rw [← integral_indicator (by measurability), heq]
  change (∫ s, f s) ≤ _
  rw [hwhole]
  have hwindow : (δ*L^(2*γ)/(4*L^2))^r ≤ (L^(2*γ)/(4*L^2))^r := by
    apply Real.rpow_le_rpow (by positivity)
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_of_le_one_left (by positivity) hδ.2
    · exact hr.le
  have hcoef : 0 ≤ C*(J*D)*width^(4*d) := by positivity
  calc
    _ ≤ C*(J*D)*width^(4*d)*L^(2*(d : ℝ))*(δ*L^(2*γ)/(4*L^2))^r := hh.2
    _ ≤ C*(J*D)*width^(4*d)*L^(2*(d : ℝ))*(L^(2*γ)/(4*L^2))^r :=
      mul_le_mul_of_nonneg_left hwindow (mul_nonneg hcoef (by positivity))
    _ = A*D*width^(4*d)*L^(2*(d : ℝ)+(2*γ-2)*r) := by
      have hscale := bilinear_minor_scale_identity hLp (by norm_num : (0 : ℝ) ≤ 1) (d : ℝ) γ ε
      simp only [one_mul,one_div] at hscale
      calc
        _ = (C*(J*D)*width^(4*d))*(L^(2*(d : ℝ))*(L^(2*γ)/(4*L^2))^r) := by ring
        _ = _ := by rw [hscale]; dsimp [A,r]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1
        (bilinear_minor_exponent_le (d : ℝ) γ ε η hγ.1.le hε.le hεη)) (by positivity)

/-- An explicit sufficient version of DH23's standing small-`η` convention.
Thus the uniform decay condition above follows from the source threshold. -/
theorem source_decay_power_ge_two_dim (d : ℕ) (hd : 3 ≤ d) {η P : ℝ}
    (hη : 0 < η) (hsmall : η ≤ 1/(2*(d : ℝ))) (hP : η^(-2 : ℝ) < P) :
    2*(d : ℝ) ≤ P := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < 2*(d : ℝ) := by linarith
  have hrec : 2*(d : ℝ) ≤ 1/η := by
    apply (le_div_iff₀ hη).mpr
    have hh := (le_div_iff₀ hdpos).mp hsmall
    nlinarith only [hh]
  have hsq := (sq_le_sq₀ hdpos.le (by positivity : (0 : ℝ) ≤ 1/η)).mpr hrec
  have heq : η^(-2 : ℝ) = (1/η)^2 := by
    rw [Real.rpow_neg hη.le, Real.rpow_two]
    field_simp
  rw [heq] at hP
  nlinarith only [hdR,hsq,hP]

end WaveTurbulence.WeylSums
