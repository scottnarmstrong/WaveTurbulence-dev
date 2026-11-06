/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WeightedSmoothMultiplier
/-! Quantitative source seminorm bounds for coordinate monomials on individual leaves. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem norm_linear_jet_le_jbr {d : ℕ} (F : Mom d →L[ℝ] ℂ) (hF : ‖F‖ ≤ 1)
    (r : ℕ) (x : Mom d) : ‖iteratedFDeriv ℝ r (fun y => F y) x‖ ≤ jbr x := by
  cases r with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    apply (F.le_opNorm x).trans
    apply (mul_le_mul_of_nonneg_right hF (norm_nonneg x)).trans
    have hj : ‖x‖ ≤ jbr x := by
      unfold jbr
      apply Real.le_sqrt_of_sq_le
      exact le_add_of_nonneg_left (by norm_num)
    simpa only [one_mul] using hj
  | succ r =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun y => F y) = fun _ => F := funext (fun y => F.fderiv)
    rw [he]
    by_cases hr : r = 0
    · subst r
      rw [norm_iteratedFDeriv_zero]
      exact hF.trans (one_le_jbr x)
    · rw [iteratedFDeriv_const_of_ne hr]
      simp only [Pi.zero_apply, norm_zero]
      exact (jbr_pos x).le

noncomputable def complexCoordinate {d : ℕ} (j : Fin d) : Mom d →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin d => ℝ) j)

theorem norm_complexCoordinate_le {d : ℕ} (j : Fin d) : ‖complexCoordinate j‖ ≤ 1 := by
  refine (complexCoordinate j).opNorm_le_bound zero_le_one ?_
  intro x
  change ‖(x j : ℂ)‖ ≤ 1 * ‖x‖
  simpa only [Complex.norm_real, one_mul] using PiLp.norm_apply_le x j

noncomputable def coordinateWord {d : ℕ} : List (Fin d) → Mom d → ℂ
  | [], _ => 1
  | j :: word, x => complexCoordinate j x * coordinateWord word x

theorem contDiff_coordinateWord {d : ℕ} (word : List (Fin d)) (A : ℕ) :
    ContDiff ℝ A (coordinateWord word) := by
  induction word with
  | nil => exact contDiff_const
  | cons j word ih => exact (complexCoordinate j).contDiff.mul ih

/-- Multiplication by a coordinate word consumes exactly its length in spatial decay.
The loss depends on the word length and the fixed derivative order, never on other leaves. -/
theorem SNorm_coordinateWord_mul {d A B : ℕ} (hd : 1 ≤ d) (word : List (Fin d))
    (f : Mom d → ℂ) (hf : ContDiff ℝ A f) (C : ℝ) (hC : 0 ≤ C)
    (hF : SNorm A (B + word.length) f ≤ ENNReal.ofReal C) :
    SNorm A B (fun x => coordinateWord word x * f x) ≤
      ENNReal.ofReal ((((2 : ℝ) ^ A * (d : ℝ) ^ A) ^ word.length) * C) := by
  induction word generalizing B with
  | nil => simpa only [coordinateWord, List.length_nil, Nat.add_zero, pow_zero, one_mul] using hF
  | cons j word ih =>
    have ht : SNorm A ((B + 1) + word.length) f ≤ ENNReal.ofReal C := by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hF
    have hb := ih (B := B + 1) ht
    have hc : ContDiff ℝ A (fun x => coordinateWord word x * f x) :=
      (contDiff_coordinateWord word A).mul hf
    have he := SNorm_mul_of_polynomial_jet_bound (B := B) (M := 1) hd
      (fun x => complexCoordinate j x) (fun x => coordinateWord word x * f x)
      (complexCoordinate j).contDiff hc 1
      (((2 : ℝ) ^ A * (d : ℝ) ^ A) ^ word.length * C) zero_le_one (by positivity)
      (fun r _ x => by simpa only [one_mul, pow_one] using
        norm_linear_jet_le_jbr (complexCoordinate j) (norm_complexCoordinate_le j) r x) hb
    have hfun : (fun x => complexCoordinate j x * (coordinateWord word x * f x)) =
        (fun x => coordinateWord (j :: word) x * f x) := by
      funext x
      simp only [coordinateWord, mul_assoc]
    rw [hfun] at he
    convert he using 1
    congr 1
    simp only [List.length_cons, pow_succ]
    ring

end WaveTurbulence.LGSpine
