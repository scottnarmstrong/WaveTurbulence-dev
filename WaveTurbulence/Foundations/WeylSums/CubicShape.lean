/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.TranslatedLatticeBound
public import WaveTurbulence.Foundations.WeylSums.CoordinateBoxSupport

/-! # The fixed cutoff shape after cubic diagonalization -/

public section
open Finset
open scoped ContDiff
namespace WaveTurbulence.WeylSums

/-- The cutoff induced by `(u,v,w)=(x+y,x-y,x+y-2z)`. -/
@[expose] noncomputable def cubicDiagonalCutoff (z : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (Fourier.chi0 ((z 0+z 1)/2)*Fourier.chi0 ((z 0-z 1)/2)*Fourier.chi0 ((z 0-z 2)/2) : ℝ)

theorem cubicDiagonalCutoff_support (z : EuclideanSpace ℝ (Fin 3))
    (hz : cubicDiagonalCutoff z ≠ 0) (i : Fin 3) : |z i| ≤ 4 := by
  have ha : Fourier.chi0 ((z 0+z 1)/2) ≠ 0 ∧ Fourier.chi0 ((z 0-z 1)/2) ≠ 0 ∧
      Fourier.chi0 ((z 0-z 2)/2) ≠ 0 := by
    simpa only [cubicDiagonalCutoff, ne_eq, Complex.ofReal_eq_zero, mul_eq_zero, not_or, and_assoc] using hz
  have h₁ : |(z 0+z 1)/2| < 1 := by
    by_contra h
    exact ha.1 (Fourier.chi0_eq_zero (not_lt.mp h))
  have h₂ : |(z 0-z 1)/2| < 1 := by
    by_contra h
    exact ha.2.1 (Fourier.chi0_eq_zero (not_lt.mp h))
  have h₃ : |(z 0-z 2)/2| < 1 := by
    by_contra h
    exact ha.2.2 (Fourier.chi0_eq_zero (not_lt.mp h))
  obtain ⟨h₁l,h₁u⟩ := abs_lt.mp h₁
  obtain ⟨h₂l,h₂u⟩ := abs_lt.mp h₂
  obtain ⟨h₃l,h₃u⟩ := abs_lt.mp h₃
  fin_cases i
  · change |z 0| ≤ 4
    apply abs_le.mpr
    constructor <;> linarith only [h₁l,h₁u,h₂l,h₂u,h₃l,h₃u]
  · change |z 1| ≤ 4
    apply abs_le.mpr
    constructor <;> linarith only [h₁l,h₁u,h₂l,h₂u,h₃l,h₃u]
  · change |z 2| ≤ 4
    apply abs_le.mpr
    constructor <;> linarith only [h₁l,h₁u,h₂l,h₂u,h₃l,h₃u]

theorem cubicDiagonalCutoff_hasCompactSupport : HasCompactSupport cubicDiagonalCutoff :=
  hasCompactSupport_of_coordinate_box _ 4 (by norm_num) cubicDiagonalCutoff_support

@[fun_prop] theorem cubicDiagonalCutoff_contDiff : ContDiff ℝ ∞ cubicDiagonalCutoff := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 3) => z i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff
  have hreal : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 3) =>
      Fourier.chi0 ((z 0+z 1)/2)*Fourier.chi0 ((z 0-z 1)/2)*Fourier.chi0 ((z 0-z 2)/2)) := by
    apply ContDiff.mul
    · apply ContDiff.mul
      · exact Fourier.chi0_contDiff.comp ((hc 0).add (hc 1) |>.div_const 2)
      · exact Fourier.chi0_contDiff.comp ((hc 0).sub (hc 1) |>.div_const 2)
    · exact Fourier.chi0_contDiff.comp ((hc 0).sub (hc 2) |>.div_const 2)
  exact Complex.ofRealCLM.contDiff.comp hreal

/-- The unrestricted transformed cubic sum is controlled by three Weyl
suprema at the single enlarged scale `20L`. -/
theorem exists_cubic_diagonal_lattice_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      ∀ (c : EuclideanSpace ℝ (Fin 3)) (s r : Fin 3 → ℝ),
      ‖∑' p : Fin 3 → ℤ, cubicDiagonalCutoff (WithLp.toLp 2 (fun i => (p i : ℝ)/L)-c)*
        e (∑ i, (s i*(p i : ℝ)^2+r i*(p i : ℝ)))‖ ≤
        C*∏ i, weylSupremum (20*L) (s i) := by
  simpa only [show (4 : ℝ)*(4+1) = 20 by norm_num] using
    exists_translated_compact_lattice_bound cubicDiagonalCutoff cubicDiagonalCutoff_hasCompactSupport
      cubicDiagonalCutoff_contDiff 4 (by norm_num) cubicDiagonalCutoff_support

end WaveTurbulence.WeylSums
