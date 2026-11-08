/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsFold.Folds

/-! # D1b-F FOLD 5: the folding extension (o82 Lemma 17.1, (17.3))

`foldExt H = kS0 · (kS1 · (kT0 · (kT1 · (kD · H ∘ foldD) ∘ foldT1) ∘ foldT0) ∘ foldS1) ∘ foldS0`:
* `foldExt_eq`: `foldExt H = H` on the unit triangle `triD` (every fold fixes it, every weight is `1` there);
* `norm_foldExt_le`: `‖foldExt H x‖ ≤ A ‖foldCut x‖` when `‖H‖ ≤ A` on `triD` (on `supp foldCut ⊂ (-1/2, 3/2)²` the
  composite fold lands in `triD`; all weights are bounded by one);
* `foldExt_norm_le`: `‖foldExt H‖_{𝔛^{1/8}} ≤ extC ‖H‖_{𝔛^{1/4}}` (five folds, each losing `2ε = 1/40`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal Real ContDiff

namespace WaveTurbulence.Flower.ProtOpsFold

/-- The unit triangle `{0 ≤ s ≤ t ≤ 1}`. -/
def triD : Set (Fin 2 → ℝ) := {x | 0 ≤ x 1 ∧ x 1 ≤ x 0 ∧ x 0 ≤ 1}

/-- One fold step `x ↦ k x · g (P x)`. -/
def foldStep (k : (Fin 2 → ℝ) → ℂ) (P : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (g : (Fin 2 → ℝ) → ℂ)
    (x : Fin 2 → ℝ) : ℂ :=
  k x * g (P x)

/-- **The folding extension.** -/
def foldExt (H : (Fin 2 → ℝ) → ℂ) : (Fin 2 → ℝ) → ℂ :=
  foldStep kS0 foldS0 (foldStep kS1 foldS1 (foldStep kT0 foldT0 (foldStep kT1 foldT1 (foldStep kD foldD H))))

/-! ## Values on the triangle -/

section Fix
variable {x : Fin 2 → ℝ} (hx : x ∈ triD)
include hx

theorem foldCut_triD : foldCut x = 1 := by
  obtain ⟨h1, h2, h3⟩ := hx
  apply foldCut_one
  exact Fin.forall_fin_two.mpr ⟨⟨by linarith, h3⟩, ⟨h1, by linarith⟩⟩

theorem foldS0_fix : foldS0 x = x := by
  ext i; fin_cases i <;> simp [foldS0, abs_of_nonneg hx.1]

theorem foldS1_fix : foldS1 x = x := by
  have : 0 ≤ 1 - x 1 := by linarith [hx.2.1, hx.2.2]
  ext i; fin_cases i <;> simp [foldS1, abs_of_nonneg this]

theorem foldT0_fix : foldT0 x = x := by
  have : 0 ≤ x 0 := by linarith [hx.1, hx.2.1]
  ext i; fin_cases i <;> simp [foldT0, abs_of_nonneg this]

theorem foldT1_fix : foldT1 x = x := by
  have : 0 ≤ 1 - x 0 := by linarith [hx.2.2]
  ext i; fin_cases i <;> simp [foldT1, abs_of_nonneg this]

theorem foldD_fix : foldD x = x := by
  ext i; fin_cases i <;> simp [foldD, max_eq_left hx.2.1, min_eq_right hx.2.1]

theorem kS0_triD : kS0 x = 1 :=
  foldK_one (foldCut_triD hx) hx.1 (by linarith [hx.1, hx.2.1])
theorem kS1_triD : kS1 x = 1 :=
  foldK_one (foldCut_triD hx) (by simp; linarith [hx.2.1, hx.2.2]) (by linarith [hx.1, hx.2.1])
theorem kT0_triD : kT0 x = 1 :=
  foldK_one (foldCut_triD hx) (by linarith [hx.1, hx.2.1]) (by linarith [hx.1])
theorem kT1_triD : kT1 x = 1 :=
  foldK_one (foldCut_triD hx) (by simp; linarith [hx.2.2]) (by linarith [hx.1])
theorem kD_triD : kD x = 1 :=
  foldK_one (foldCut_triD hx) (by simp; linarith [hx.2.1]) (by linarith [hx.1])

end Fix

/-- **The extension agrees with `H` on the triangle.** -/
theorem foldExt_eq (H : (Fin 2 → ℝ) → ℂ) {x : Fin 2 → ℝ} (hx : x ∈ triD) : foldExt H x = H x := by
  unfold foldExt foldStep
  rw [kS0_triD hx, foldS0_fix hx, kS1_triD hx, foldS1_fix hx, kT0_triD hx, foldT0_fix hx,
    kT1_triD hx, foldT1_fix hx, kD_triD hx, foldD_fix hx]
  ring

/-! ## The supremum bound -/

theorem r_mem {a : ℝ} (h : |a| ≤ 2) : 0 ≤ 1 - abs (1 - |a|) ∧ 1 - abs (1 - |a|) ≤ 1 := by
  have h0 := abs_nonneg a
  constructor
  · have : abs (1 - |a|) ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · linarith [abs_nonneg (1 - |a|)]

theorem foldAll_mem {x : Fin 2 → ℝ} (h : foldCut x ≠ 0) :
    foldD (foldT1 (foldT0 (foldS1 (foldS0 x)))) ∈ triD := by
  have h0 := mem_of_foldCut_ne_zero h 0
  have h1 := mem_of_foldCut_ne_zero h 1
  have ha : |x 0| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |x 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨u0, u1⟩ := r_mem ha
  obtain ⟨v0, v1⟩ := r_mem hb
  simp only [triD, mem_ofPred_eq, foldD, foldT1, foldT0, foldS1, foldS0, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  refine ⟨le_min u0 v0, min_le_max, max_le u1 v1⟩

theorem norm_kS0_le (x : Fin 2 → ℝ) : ‖kS0 x‖ ≤ ‖foldCut x‖ := norm_foldK_le _ _ x
theorem norm_kS1_le (x : Fin 2 → ℝ) : ‖kS1 x‖ ≤ 1 := (norm_foldK_le _ _ x).trans (norm_foldCut_le x)
theorem norm_kT0_le (x : Fin 2 → ℝ) : ‖kT0 x‖ ≤ 1 := (norm_foldK_le _ _ x).trans (norm_foldCut_le x)
theorem norm_kT1_le (x : Fin 2 → ℝ) : ‖kT1 x‖ ≤ 1 := (norm_foldK_le _ _ x).trans (norm_foldCut_le x)
theorem norm_kD_le (x : Fin 2 → ℝ) : ‖kD x‖ ≤ 1 := (norm_foldK_le _ _ x).trans (norm_foldCut_le x)

/-- **The supremum bound** (the extension uses only values on `triD`). -/
theorem norm_foldExt_le {H : (Fin 2 → ℝ) → ℂ} {A : ℝ} (hA : ∀ y ∈ triD, ‖H y‖ ≤ A)
    (x : Fin 2 → ℝ) : ‖foldExt H x‖ ≤ A * ‖foldCut x‖ := by
  have hA0 : 0 ≤ A := by
    have h0 : (0 : Fin 2 → ℝ) ∈ triD := by simp [triD]
    exact (norm_nonneg _).trans (hA 0 h0)
  by_cases hc : foldCut x = 0
  · have hk : kS0 x = 0 := by
      have := norm_kS0_le x; rw [hc, norm_zero] at this; exact norm_le_zero_iff.mp this
    simp [foldExt, foldStep, hk, hc]
  · have hmem := hA _ (foldAll_mem hc)
    unfold foldExt foldStep
    simp only [norm_mul]
    have e1 := norm_kS1_le (foldS0 x)
    have e2 := norm_kT0_le (foldS1 (foldS0 x))
    have e3 := norm_kT1_le (foldT0 (foldS1 (foldS0 x)))
    have e4 := norm_kD_le (foldT1 (foldT0 (foldS1 (foldS0 x))))
    have e0 := norm_kS0_le x
    have p1 := norm_nonneg (kS1 (foldS0 x))
    have p2 := norm_nonneg (kT0 (foldS1 (foldS0 x)))
    have p3 := norm_nonneg (kT1 (foldT0 (foldS1 (foldS0 x))))
    have p4 := norm_nonneg (kD (foldT1 (foldT0 (foldS1 (foldS0 x)))))
    have p5 := norm_nonneg (H (foldD (foldT1 (foldT0 (foldS1 (foldS0 x))))))
    have p0 := norm_nonneg (kS0 x)
    calc ‖kS0 x‖ * (‖kS1 (foldS0 x)‖ * (‖kT0 (foldS1 (foldS0 x))‖ * (‖kT1 (foldT0 (foldS1 (foldS0 x)))‖ *
          (‖kD (foldT1 (foldT0 (foldS1 (foldS0 x))))‖ * ‖H (foldD (foldT1 (foldT0 (foldS1 (foldS0 x)))))‖))))
        ≤ ‖foldCut x‖ * (1 * (1 * (1 * (1 * A)))) := by gcongr
      _ = A * ‖foldCut x‖ := by ring

/-! ## Continuity and the norm bound -/

theorem foldStep_continuous {k : (Fin 2 → ℝ) → ℂ} {P : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {g : (Fin 2 → ℝ) → ℂ} (hk : Continuous k) (hP : Continuous P) (hg : Continuous g) :
    Continuous (foldStep k P g) := hk.mul (hg.comp hP)

theorem kS0_continuous : Continuous kS0 := foldK_continuous (by fun_prop) (by fun_prop)
theorem kS1_continuous : Continuous kS1 := foldK_continuous (by fun_prop) (by fun_prop)
theorem kT0_continuous : Continuous kT0 := foldK_continuous (by fun_prop) (by fun_prop)
theorem kT1_continuous : Continuous kT1 := foldK_continuous (by fun_prop) (by fun_prop)
theorem kD_continuous : Continuous kD := foldK_continuous (by fun_prop) (by fun_prop)

theorem foldExt_continuous {H : (Fin 2 → ℝ) → ℂ} (hH : Continuous H) : Continuous (foldExt H) :=
  foldStep_continuous kS0_continuous foldS0_continuous
    (foldStep_continuous kS1_continuous foldS1_continuous
      (foldStep_continuous kT0_continuous foldT0_continuous
        (foldStep_continuous kT1_continuous foldT1_continuous
          (foldStep_continuous kD_continuous foldD_continuous hH))))

/-- The loss per kink factor. -/
def epsF : ℝ := 1 / 80

/-- The extension constant (five folds). -/
def extC : ℝ≥0∞ :=
  foldC (5 / 40) epsF (fun y => y 1 + (y 0 + 1)) * foldC (6 / 40) epsF (fun y => 1 - y 1 + (y 0 + 1)) *
    foldC (7 / 40) epsF (fun y => y 0 + (y 1 + 1)) * foldC (8 / 40) epsF (fun y => 1 - y 0 + (y 1 + 1)) *
    foldC (9 / 40) epsF (fun y => y 0 - y 1 + (y 1 + 1))

theorem extC_lt_top : extC < ⊤ := by
  unfold extC
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) ?_) ?_) ?_ <;>
    exact foldC_lt_top _ _ (by fun_prop)

theorem step_lt_top {C N : ℝ≥0∞} {M : ℝ≥0∞} (hC : C < ⊤) (hN : N < ⊤) (h : M ≤ C * N) : M < ⊤ :=
  h.trans_lt (ENNReal.mul_lt_top hC hN)

/-- **The norm bound of the extension** `‖foldExt H‖_{𝔛^{1/8}} ≤ extC ‖H‖_{𝔛^{1/4}}`. -/
theorem foldExt_norm_le {H : (Fin 2 → ℝ) → ℂ} (hHc : Continuous H) (hH : timeFourierNorm (1 / 4) H < ⊤) :
    timeFourierNorm (1 / 8) (foldExt H) ≤ extC * timeFourierNorm (1 / 4) H := by
  have hε : (0 : ℝ) < epsF := by norm_num [epsF]
  set g1 := foldStep kD foldD H with hg1
  set g2 := foldStep kT1 foldT1 g1 with hg2
  set g3 := foldStep kT0 foldT0 g2 with hg3
  set g4 := foldStep kS1 foldS1 g3 with hg4
  have c1 : Continuous g1 := foldStep_continuous kD_continuous foldD_continuous hHc
  have c2 : Continuous g2 := foldStep_continuous kT1_continuous foldT1_continuous c1
  have c3 : Continuous g3 := foldStep_continuous kT0_continuous foldT0_continuous c2
  have c4 : Continuous g4 := foldStep_continuous kS1_continuous foldS1_continuous c3
  have b1 := fold_D_le (s := 9 / 40) (by norm_num) hε (by norm_num [epsF]) hHc
    (by rw [show (9 / 40 : ℝ) + 2 * epsF = 1 / 4 by norm_num [epsF]]; exact hH)
  rw [show (9 / 40 : ℝ) + 2 * epsF = 1 / 4 by norm_num [epsF]] at b1
  change timeFourierNorm (9 / 40) g1 ≤ _ at b1
  have f1 : timeFourierNorm (9 / 40) g1 < ⊤ := step_lt_top (foldC_lt_top _ _ (by fun_prop)) hH b1
  have b2 := fold_T1_le (s := 8 / 40) (by norm_num) hε (by norm_num [epsF]) c1
    (by rw [show (8 / 40 : ℝ) + 2 * epsF = 9 / 40 by norm_num [epsF]]; exact f1)
  rw [show (8 / 40 : ℝ) + 2 * epsF = 9 / 40 by norm_num [epsF]] at b2
  change timeFourierNorm (8 / 40) g2 ≤ _ at b2
  have f2 : timeFourierNorm (8 / 40) g2 < ⊤ := step_lt_top (foldC_lt_top _ _ (by fun_prop)) f1 b2
  have b3 := fold_T0_le (s := 7 / 40) (by norm_num) hε (by norm_num [epsF]) c2
    (by rw [show (7 / 40 : ℝ) + 2 * epsF = 8 / 40 by norm_num [epsF]]; exact f2)
  rw [show (7 / 40 : ℝ) + 2 * epsF = 8 / 40 by norm_num [epsF]] at b3
  change timeFourierNorm (7 / 40) g3 ≤ _ at b3
  have f3 : timeFourierNorm (7 / 40) g3 < ⊤ := step_lt_top (foldC_lt_top _ _ (by fun_prop)) f2 b3
  have b4 := fold_S1_le (s := 6 / 40) (by norm_num) hε (by norm_num [epsF]) c3
    (by rw [show (6 / 40 : ℝ) + 2 * epsF = 7 / 40 by norm_num [epsF]]; exact f3)
  rw [show (6 / 40 : ℝ) + 2 * epsF = 7 / 40 by norm_num [epsF]] at b4
  change timeFourierNorm (6 / 40) g4 ≤ _ at b4
  have f4 : timeFourierNorm (6 / 40) g4 < ⊤ := step_lt_top (foldC_lt_top _ _ (by fun_prop)) f3 b4
  have b5 := fold_S0_le (s := 5 / 40) (by norm_num) hε (by norm_num [epsF]) c4
    (by rw [show (5 / 40 : ℝ) + 2 * epsF = 6 / 40 by norm_num [epsF]]; exact f4)
  rw [show (5 / 40 : ℝ) + 2 * epsF = 6 / 40 by norm_num [epsF]] at b5
  change timeFourierNorm (5 / 40) (foldExt H) ≤ _ at b5
  rw [show (1 / 8 : ℝ) = 5 / 40 by norm_num]
  calc timeFourierNorm (5 / 40) (foldExt H)
      ≤ foldC (5 / 40) epsF (fun y => y 1 + (y 0 + 1)) * (foldC (6 / 40) epsF (fun y => 1 - y 1 + (y 0 + 1)) *
          (foldC (7 / 40) epsF (fun y => y 0 + (y 1 + 1)) * (foldC (8 / 40) epsF (fun y => 1 - y 0 + (y 1 + 1)) *
            (foldC (9 / 40) epsF (fun y => y 0 - y 1 + (y 1 + 1)) * timeFourierNorm (1 / 4) H)))) := by
        refine b5.trans ?_; gcongr
        refine b4.trans ?_; gcongr
        refine b3.trans ?_; gcongr
        refine b2.trans ?_; gcongr
    _ = extC * timeFourierNorm (1 / 4) H := by unfold extC; ring

end WaveTurbulence.Flower.ProtOpsFold
