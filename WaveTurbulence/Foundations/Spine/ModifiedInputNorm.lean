/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoordinateMonomialNorm
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeNorm
public import WaveTurbulence.Foundations.Sumint.MultiIndices
public import WaveTurbulence.Foundations.XChain.SNormRealPart
/-! The explicit individually weighted and differentiated source inputs have finite low-order norms. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset NormBridgeScratch

theorem coordinateWord_eq_ofReal {d : ℕ} (word : List (Fin d)) (x : Mom d) :
    coordinateWord word x = (((word.map (fun j => x j)).prod : ℝ) : ℂ) := by
  induction word with
  | nil => rfl
  | cons j word ih =>
    change (x j : ℂ) * coordinateWord word x = _
    rw [ih, List.map_cons, List.prod_cons, Complex.ofReal_mul]

/-- The leaf modification is exactly the one used by the exported multilinear source
estimates: a real coordinate monomial times the real part of the coordinate derivative. -/
theorem SNormR_coordinate_iterPartial_bound {d A B : ℕ} (hd : 1 ≤ d)
    (word : List (Fin d)) (ρ : Fin d → ℕ) (f : Mom d → ℂ)
    (hf : ContDiff ℝ (A + ∑ j, ρ j : ℕ) f)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : SNorm (A + ∑ j, ρ j) (B + word.length) f ≤ ENNReal.ofReal C) :
    SNormR A B (fun x => (word.map (fun j => x j)).prod * (iterPartial ρ f x).re) ≤
      ENNReal.ofReal ((((2 : ℝ) ^ A * (d : ℝ) ^ A) ^ word.length) *
        ((d : ℝ) ^ (A + ∑ j, ρ j) * C)) := by
  have hc : ContDiff ℝ (A + (canonical ρ).length : ℕ) f := by
    simpa only [canonical_length] using hf
  have hfin : SNorm (A + (canonical ρ).length) (B + word.length) f ≤ ENNReal.ofReal C := by
    simpa only [canonical_length] using hF
  have hdif := SNorm_wordD_bound hd (canonical ρ) f hc C hC hfin
  have hcont := wordD_contDiff (canonical ρ) A hc
  have hbound := SNorm_coordinateWord_mul hd word (wordD (canonical ρ) f) hcont
    ((d : ℝ) ^ (A + (canonical ρ).length) * C) (by positivity) hdif
  have hprod : ContDiff ℝ A (fun x => coordinateWord word x * wordD (canonical ρ) f x) :=
    (contDiff_coordinateWord word A).mul hcont
  have hr := SNormR_realPart_bound _ hprod _ (by positivity) hbound
  have he : (fun x => (coordinateWord word x * wordD (canonical ρ) f x).re) =
      (fun x => (word.map (fun j => x j)).prod * (iterPartial ρ f x).re) := by
    funext x
    rw [coordinateWord_eq_ofReal, iterPartial_eq_wordD]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he] at hr
  simpa only [canonical_length] using hr

end WaveTurbulence.LGSpine
