/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsFold.Synth

/-! # D1b-F FOLD 4: the five folds of the unit triangle (o82 Lemma 17.1)

`D = {0 ≤ s ≤ t ≤ 1}` (`t = x 0`, `s = x 1`). The folds `s ↦ |s|`, `s ↦ 1 - |1 - s|`, `t ↦ |t|`, `t ↦ 1 - |1 - t|`
and `(t, s) ↦ (max, min)` fix `D` pointwise. Each carries the weight `foldK ℓ₁ ℓ₂` with fold coordinate `ℓ₁ ≥ 0` on
`D` and tangential coordinate `ℓ₂ = (other) + 1`. Each fold atom factors exactly through a kink tensor (the sorting
fold through the shear `(t,s) ↦ (t-s, s)`, since `a max + b min = (a+b) s + ((a+b)/2)(t-s) + ((a-b)/2)|t-s|`), so
`‖k · H ∘ P‖_{𝔛^s} ≤ C ‖H‖_{𝔛^{s+2ε}}` (o82 (17.2)). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal Real ContDiff

namespace WaveTurbulence.Flower.ProtOpsFold

theorem continuous_vec2 {f g : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (![f x, g x] : Fin 2 → ℝ) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa using hf
  · simpa using hg

theorem pairing2 (l v : Fin 2 → ℝ) : timePairing 2 l v = l 0 * v 0 + l 1 * v 1 := by
  change l ⬝ᵥ v = _
  simp [dotProduct, Fin.sum_univ_two]

/-! ## The folds and their weights -/

/-- `s ↦ |s|`. -/
def foldS0 (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 0, |x 1|]
/-- `s ↦ 1 - |1 - s|`. -/
def foldS1 (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 0, 1 - |1 - x 1|]
/-- `t ↦ |t|`. -/
def foldT0 (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![|x 0|, x 1]
/-- `t ↦ 1 - |1 - t|`. -/
def foldT1 (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![1 - |1 - x 0|, x 1]
/-- `(t, s) ↦ (max, min)`. -/
def foldD (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![max (x 0) (x 1), min (x 0) (x 1)]

/-- Weights: fold coordinate, then tangential coordinate. -/
def kS0 : (Fin 2 → ℝ) → ℂ := foldK (fun x => x 1) (fun x => x 0 + 1)
def kS1 : (Fin 2 → ℝ) → ℂ := foldK (fun x => 1 - x 1) (fun x => x 0 + 1)
def kT0 : (Fin 2 → ℝ) → ℂ := foldK (fun x => x 0) (fun x => x 1 + 1)
def kT1 : (Fin 2 → ℝ) → ℂ := foldK (fun x => 1 - x 0) (fun x => x 1 + 1)
def kD : (Fin 2 → ℝ) → ℂ := foldK (fun x => x 0 - x 1) (fun x => x 1 + 1)

theorem foldS0_continuous : Continuous foldS0 := continuous_vec2 (by fun_prop) (by fun_prop)
theorem foldS1_continuous : Continuous foldS1 := continuous_vec2 (by fun_prop) (by fun_prop)
theorem foldT0_continuous : Continuous foldT0 := continuous_vec2 (by fun_prop) (by fun_prop)
theorem foldT1_continuous : Continuous foldT1 := continuous_vec2 (by fun_prop) (by fun_prop)
theorem foldD_continuous : Continuous foldD := continuous_vec2 (by fun_prop) (by fun_prop)

theorem max_eq_abs (a b : ℝ) : max a b = b + ((a - b) + |a - b|) / 2 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring

theorem min_eq_abs (a b : ℝ) : min a b = b + ((a - b) - |a - b|) / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-! ## Exact factorization of the fold atoms -/

theorem foldAtom_S0 (l x : Fin 2 → ℝ) : foldAtom kS0 foldS0 l x =
    foldN (fun y => y 1 + (y 0 + 1)) x *
      (1 * tensor2 (kinkAtom (-1) (l 0) 0) (kinkAtom 0 0 (l 1)) (id x)) := by
  simp only [foldAtom, kS0, foldK, foldS0, pairing2, tensor2, kinkAtom, Real.fourierChar_apply, id,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, sub_neg_eq_add, sub_zero, mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem foldAtom_S1 (l x : Fin 2 → ℝ) : foldAtom kS1 foldS1 l x =
    foldN (fun y => 1 - y 1 + (y 0 + 1)) x *
      ((Real.fourierChar (l 1) : ℂ) * tensor2 (kinkAtom (-1) (l 0) 0) (kinkAtom 1 0 (-l 1)) (id x)) := by
  simp only [foldAtom, kS1, foldK, foldS1, pairing2, tensor2, kinkAtom, Real.fourierChar_apply, id,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add, mul_assoc]
  rw [abs_sub_comm 1 (x 1)]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem foldAtom_T0 (l x : Fin 2 → ℝ) : foldAtom kT0 foldT0 l x =
    foldN (fun y => y 0 + (y 1 + 1)) x *
      (1 * tensor2 (kinkAtom 0 0 (l 0)) (kinkAtom (-1) (l 1) 0) (id x)) := by
  simp only [foldAtom, kT0, foldK, foldT0, pairing2, tensor2, kinkAtom, Real.fourierChar_apply, id,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, sub_neg_eq_add, sub_zero, mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem foldAtom_T1 (l x : Fin 2 → ℝ) : foldAtom kT1 foldT1 l x =
    foldN (fun y => 1 - y 0 + (y 1 + 1)) x *
      ((Real.fourierChar (l 0) : ℂ) * tensor2 (kinkAtom 1 0 (-l 0)) (kinkAtom (-1) (l 1) 0) (id x)) := by
  simp only [foldAtom, kT1, foldK, foldT1, pairing2, tensor2, kinkAtom, Real.fourierChar_apply, id,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add, mul_assoc]
  rw [abs_sub_comm 1 (x 0)]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem foldAtom_D (l x : Fin 2 → ℝ) : foldAtom kD foldD l x =
    foldN (fun y => y 0 - y 1 + (y 1 + 1)) x *
      (1 * tensor2 (kinkAtom 0 ((l 0 + l 1) / 2) ((l 0 - l 1) / 2)) (kinkAtom (-1) (l 0 + l 1) 0)
        (shear x)) := by
  simp only [foldAtom, kD, foldK, foldD, shear, pairing2, tensor2, kinkAtom, Real.fourierChar_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, sub_neg_eq_add, sub_zero, mul_assoc,
    max_eq_abs, min_eq_abs]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The five fold estimates -/

theorem abs_le_l (l : Fin 2 → ℝ) : |l 0| ≤ |l 0| + |l 1| ∧ |l 1| ≤ |l 0| + |l 1| ∧
    |l 0 + l 1| ≤ |l 0| + |l 1| ∧ |(l 0 + l 1) / 2| ≤ |l 0| + |l 1| ∧
    |(l 0 - l 1) / 2| ≤ |l 0| + |l 1| ∧ |(0 : ℝ)| ≤ |l 0| + |l 1| ∧
    |-l 0| ≤ |l 0| + |l 1| ∧ |-l 1| ≤ |l 0| + |l 1| := by
  have h0 := abs_nonneg (l 0)
  have h1 := abs_nonneg (l 1)
  have ha := abs_add_le (l 0) (l 1)
  have hs := abs_sub (l 0) (l 1)
  refine ⟨by linarith, by linarith, ha, ?_, ?_, by rw [abs_zero]; linarith, by rw [abs_neg]; linarith,
    by rw [abs_neg]; linarith⟩
  · rw [abs_div, abs_two]; linarith
  · rw [abs_div, abs_two]; linarith

section
variable {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (hse : s + ε ≤ 1)
  {H : (Fin 2 → ℝ) → ℂ} (hHc : Continuous H) (hH : timeFourierNorm (s + 2 * ε) H < ⊤)
include hs hε hse hHc hH

theorem fold_S0_le :
    timeFourierNorm s (fun x => kS0 x * H (foldS0 x)) ≤
      foldC s ε (fun y => y 1 + (y 0 + 1)) * timeFourierNorm (s + 2 * ε) H := by
  have L := abs_le_l
  exact fold_norm_le (by linarith) (foldK_continuous (by fun_prop) (by fun_prop))
    (foldK_integrable (by fun_prop) (by fun_prop)) foldS0_continuous
    (fun l => foldAtom_norm_le hs hε hse (by fun_prop) (Or.inl rfl) l (by simp) _ _ _ _ _ _
      (L l).1 (L l).2.2.2.2.2.1 (L l).2.2.2.2.2.1 (L l).2.1 (foldAtom_S0 l)) hHc hH

theorem fold_S1_le :
    timeFourierNorm s (fun x => kS1 x * H (foldS1 x)) ≤
      foldC s ε (fun y => 1 - y 1 + (y 0 + 1)) * timeFourierNorm (s + 2 * ε) H := by
  have L := abs_le_l
  exact fold_norm_le (by linarith) (foldK_continuous (by fun_prop) (by fun_prop))
    (foldK_integrable (by fun_prop) (by fun_prop)) foldS1_continuous
    (fun l => foldAtom_norm_le hs hε hse (by fun_prop) (Or.inl rfl) l (by simp) _ _ _ _ _ _
      (L l).1 (L l).2.2.2.2.2.1 (L l).2.2.2.2.2.1 (L l).2.2.2.2.2.2.2 (foldAtom_S1 l)) hHc hH

theorem fold_T0_le :
    timeFourierNorm s (fun x => kT0 x * H (foldT0 x)) ≤
      foldC s ε (fun y => y 0 + (y 1 + 1)) * timeFourierNorm (s + 2 * ε) H := by
  have L := abs_le_l
  exact fold_norm_le (by linarith) (foldK_continuous (by fun_prop) (by fun_prop))
    (foldK_integrable (by fun_prop) (by fun_prop)) foldT0_continuous
    (fun l => foldAtom_norm_le hs hε hse (by fun_prop) (Or.inl rfl) l (by simp) _ _ _ _ _ _
      (L l).2.2.2.2.2.1 (L l).1 (L l).2.1 (L l).2.2.2.2.2.1 (foldAtom_T0 l)) hHc hH

theorem fold_T1_le :
    timeFourierNorm s (fun x => kT1 x * H (foldT1 x)) ≤
      foldC s ε (fun y => 1 - y 0 + (y 1 + 1)) * timeFourierNorm (s + 2 * ε) H := by
  have L := abs_le_l
  exact fold_norm_le (by linarith) (foldK_continuous (by fun_prop) (by fun_prop))
    (foldK_integrable (by fun_prop) (by fun_prop)) foldT1_continuous
    (fun l => foldAtom_norm_le hs hε hse (by fun_prop) (Or.inl rfl) l (by simp) _ _ _ _ _ _
      (L l).2.2.2.2.2.1 (L l).2.2.2.2.2.2.1 (L l).2.1 (L l).2.2.2.2.2.1 (foldAtom_T1 l)) hHc hH

theorem fold_D_le :
    timeFourierNorm s (fun x => kD x * H (foldD x)) ≤
      foldC s ε (fun y => y 0 - y 1 + (y 1 + 1)) * timeFourierNorm (s + 2 * ε) H := by
  have L := abs_le_l
  exact fold_norm_le (by linarith) (foldK_continuous (by fun_prop) (by fun_prop))
    (foldK_integrable (by fun_prop) (by fun_prop)) foldD_continuous
    (fun l => foldAtom_norm_le hs hε hse (by fun_prop) (Or.inr rfl) l (by simp) _ _ _ _ _ _
      (L l).2.2.2.1 (L l).2.2.2.2.1 (L l).2.2.1 (L l).2.2.2.2.2.1 (foldAtom_D l)) hHc hH

end

end WaveTurbulence.Flower.ProtOpsFold
