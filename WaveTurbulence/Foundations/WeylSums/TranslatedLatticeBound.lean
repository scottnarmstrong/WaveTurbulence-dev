/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.FourierLatticeBound
public import WaveTurbulence.Foundations.WeylSums.FourierTranslations

/-!
# Uniform translated compact lattice bounds

The original joint cutoff is arbitrary. Its support radius fixes one
constant enlargement of the auxiliary Weyl cutoff; Fourier translation
preserves the coefficient `L¹` norm. No plateau estimate is assumed.
-/

public section
open MeasureTheory Finset
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- The generic compact lattice reduction is uniform in all real spatial
translations, with the support premise stated geometrically. -/
theorem exists_translated_compact_lattice_bound {m : ℕ}
    (χ : EuclideanSpace ℝ (Fin m) → ℂ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ∞ χ) (R : ℝ) (hR : 0 ≤ R)
    (hbox : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (c : EuclideanSpace ℝ (Fin m)) (s r : Fin m → ℝ),
      ‖∑' p : Fin m → ℤ, χ (WithLp.toLp 2 (fun i => (p i : ℝ)/L)-c) *
        e (∑ i, (s i*(p i : ℝ)^2+r i*(p i : ℝ)))‖ ≤
        C * ∏ i, weylSupremum (4*(R+1)*L) (s i) := by
  obtain ⟨F, hF, htrans⟩ := exists_uniform_translated_fourier_representation χ hc hs
  have hFn : 0 ≤ ∫ ξ, ‖F ξ‖ := integral_nonneg (fun ξ => norm_nonneg _)
  refine ⟨(∫ ξ, ‖F ξ‖)+1, by positivity, ?_⟩
  intro L hL c s r
  have hLp : 0 < L := by linarith only [hL]
  let M := 4*(R+1)*L
  have hMp : 0 < M := by dsimp [M]; positivity
  let h : Fin m → ℤ := fun i => round (L*c i)
  obtain ⟨Fₐ, hFa, hnorm, hrep⟩ := htrans c
  have hplateau (n : Fin m → ℤ)
      (hn : χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)-c) ≠ 0) (i : Fin m) :
      weylCutoff ((n i : ℝ)/M) = 1 := by
    have hx := hbox _ hn i
    change |((n i : ℝ)+(h i : ℝ))/L-c i| ≤ R at hx
    have hr := abs_sub_round (L*c i)
    change |L*c i-(h i : ℝ)| ≤ 1/2 at hr
    obtain ⟨hxl,hxu⟩ := abs_le.mp hx
    obtain ⟨hrl,hru⟩ := abs_le.mp hr
    have hl := (le_div_iff₀ hLp).mp (show c i-R ≤ ((n i : ℝ)+(h i : ℝ))/L by linarith only [hxl])
    have hu := (div_le_iff₀ hLp).mp (show ((n i : ℝ)+(h i : ℝ))/L ≤ c i+R by linarith only [hxu])
    have hni : |(n i : ℝ)/M| ≤ 1/2 := by
      rw [abs_div, abs_of_pos hMp, div_le_iff₀ hMp]
      apply abs_le.mpr
      dsimp [M]
      have hRL : 0 ≤ R*L := mul_nonneg hR hLp.le
      constructor <;> nlinarith only [hl,hu,hrl,hru,hL,hRL]
    simp only [weylCutoff, Fourier.chi0_eq_one hni, Complex.ofReal_one]
  have hh := norm_lattice_sum_le_of_fourier_representation
    (fun x => χ (x-c)) Fₐ hFa hrep L M h hLp hMp hplateau s r
  have heq : (∑' n : Fin m → ℤ,
      χ (WithLp.toLp 2 (fun i => ((n i : ℝ)+h i)/L)-c) *
        e (∑ i, (s i*((n i : ℝ)+h i)^2+r i*((n i : ℝ)+h i)))) =
      ∑' p : Fin m → ℤ, χ (WithLp.toLp 2 (fun i => (p i : ℝ)/L)-c) *
        e (∑ i, (s i*(p i : ℝ)^2+r i*(p i : ℝ))) := by
    simpa only [Equiv.coe_addRight, Pi.add_apply, Int.cast_add] using
      (Equiv.addRight h).tsum_eq (fun p : Fin m → ℤ =>
        χ (WithLp.toLp 2 (fun i => (p i : ℝ)/L)-c) *
          e (∑ i, (s i*(p i : ℝ)^2+r i*(p i : ℝ))))
  rw [heq, hnorm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith)
    (prod_nonneg (fun i _ => weylSupremum_nonneg hMp _)))

end WaveTurbulence.WeylSums
