/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkUnique

/-!
# The `a`-system as an ODE in weighted `ℓ¹`

In the weighted coordinates `yₙ = (1 + ‖n‖)^{d+1} aₙ`, the system (akeqn)–(akeqn2) is the ODE
`y' = flowField L γ δ t y` on the Banach space `ℓ¹(ℤ^d)` (`L1 d`). The weighted `ℓ¹` space is an
algebra for the cubic nonlinearity (submultiplicative weights, `tsum_wt_mul_tripleAbs_le`), so

* `norm_flowField_le`: `‖flowField t y‖ ≤ κ ‖y‖³`;
* `norm_flowField_sub_le`: `‖flowField t y - flowField t y'‖ ≤ κ (‖y‖² + ‖y‖‖y'‖ + ‖y'‖²) ‖y - y'‖`,

with `κ = |δ / (2 L^{d-γ})|`. A bounded `y` gives the class `Z^{d+1}` automatically.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-- `ℓ¹(ℤ^d)` with complex values. -/
abbrev L1 (d : ℕ) := lp (fun _ : Fin d → ℤ => ℂ) 1

theorem L1.norm_eq (y : L1 d) : ‖y‖ = ∑' n, ‖y n‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp)]
  simp

theorem L1.summable (y : L1 d) : Summable fun n => ‖y n‖ := by
  simpa using (lp.memℓp y).summable (by simp)

/-- An element of `ℓ¹` from an absolutely summable family. -/
@[expose] def L1.mk (f : (Fin d → ℤ) → ℂ) (hf : Summable fun n => ‖f n‖) : L1 d :=
  ⟨f, show Memℓp f 1 from (memℓp_gen_iff (by simp)).2 (by simpa using hf)⟩

@[simp] theorem L1.mk_apply (f : (Fin d → ℤ) → ℂ) (hf : Summable fun n => ‖f n‖) (n : Fin d → ℤ) :
    L1.mk f hf n = f n := rfl

theorem L1.tsum_enorm (y : L1 d) : ∑' n, ‖y n‖ₑ = ENNReal.ofReal ‖y‖ := by
  rw [L1.norm_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (L1.summable y)]
  simp [ofReal_norm]

theorem summable_norm_of_tsum_enorm_ne_top {f : (Fin d → ℤ) → ℂ} (h : ∑' n, ‖f n‖ₑ ≠ ∞) :
    Summable fun n => ‖f n‖ := by
  simpa [toReal_enorm] using ENNReal.summable_toReal h

theorem tsum_norm_le_of_tsum_enorm_le {f : (Fin d → ℤ) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∑' n, ‖f n‖ₑ ≤ ENNReal.ofReal C) : ∑' n, ‖f n‖ ≤ C := by
  have hfin : ∑' n, ‖f n‖ₑ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.tsum_toReal_eq (fun n => enorm_ne_top), ENNReal.toReal_ofReal hC] at h1

/-! ### Weights -/

/-- The weight `(1 + ‖n‖)^{d+1}`. -/
@[expose] def flowWeight (n : Fin d → ℤ) : ℝ := (1 + ‖n‖) ^ (d + 1)

theorem flowWeight_pos (n : Fin d → ℤ) : 0 < flowWeight n := by
  unfold flowWeight; positivity

theorem wt_eq_ofReal_flowWeight (n : Fin d → ℤ) : wt (d + 1) n = ENNReal.ofReal (flowWeight n) := by
  rw [wt, flowWeight, ENNReal.ofReal_pow (by positivity)]

/-- The unweighted coefficients `aₙ = yₙ / (1 + ‖n‖)^{d+1}`. -/
@[expose] def unweight (y : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ := y n / (flowWeight n : ℂ)

theorem norm_unweight_le (y : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ‖unweight y n‖ ≤ ‖y n‖ := by
  rw [unweight, norm_div, Complex.norm_real, Real.norm_of_nonneg (flowWeight_pos n).le]
  exact div_le_self (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg n]))

theorem wt_mul_enorm_unweight (y : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    wt (d + 1) n * ‖unweight y n‖ₑ = ‖y n‖ₑ := by
  rw [wt_eq_ofReal_flowWeight, unweight, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (flowWeight_pos n).le, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (flowWeight_pos n).le, mul_div_cancel₀ _ (flowWeight_pos n).ne']

theorem wnorm_unweight (y : L1 d) : wnorm (d + 1) (unweight y) = ENNReal.ofReal ‖y‖ := by
  simp only [wnorm, wt_mul_enorm_unweight]
  exact L1.tsum_enorm y

theorem summable_norm_unweight (y : L1 d) : Summable fun n => ‖unweight y n‖ :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_unweight_le y) (L1.summable y)

/-! ### The vector field -/

/-- The weighted right side of (akeqn): `n ↦ (1 + ‖n‖)^{d+1} 𝒞₊(a, ā, a)ₙ(t)` with `a = unweight y`. -/
@[expose] def flowTerm (L γ δ t : ℝ) (y : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  (flowWeight n : ℂ) * aNonlin L γ δ 1 t (unweight y) (fun m => (starRingEnd ℂ) (unweight y m))
    (unweight y) n

theorem enorm_flowTerm_le (L γ δ t : ℝ) (y : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    ‖flowTerm L γ δ t y n‖ₑ ≤ ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))| *
      (wt (d + 1) n * tripleAbs (unweight y) (fun m => (starRingEnd ℂ) (unweight y m))
        (unweight y) n) := by
  rw [flowTerm, enorm_mul, ← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (flowWeight_pos n).le, ← wt_eq_ofReal_flowWeight, mul_left_comm]
  gcongr
  exact enorm_aNonlin_le L γ δ t _ _ _ n

theorem tsum_enorm_flowTerm_le (L γ δ t : ℝ) (y : L1 d) :
    ∑' n, ‖flowTerm L γ δ t y n‖ₑ ≤
      ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))| * ENNReal.ofReal ‖y‖ ^ 3 := by
  calc ∑' n, ‖flowTerm L γ δ t y n‖ₑ ≤ ∑' n, ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))| *
        (wt (d + 1) n * tripleAbs (unweight y) (fun m => (starRingEnd ℂ) (unweight y m))
          (unweight y) n) := ENNReal.tsum_le_tsum fun n => enorm_flowTerm_le L γ δ t y n
    _ ≤ ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))| *
        (wnorm (d + 1) (unweight y) * wnorm (d + 1) (fun m => (starRingEnd ℂ) (unweight y m)) *
          wnorm (d + 1) (unweight y)) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact tsum_wt_mul_tripleAbs_le _ _ _ _
    _ = _ := by
        have hc : wnorm (d + 1) (fun m => (starRingEnd ℂ) (unweight y m)) =
            wnorm (d + 1) (unweight y) := by
          simp only [wnorm, ← ofReal_norm, Complex.norm_conj]
        rw [hc, wnorm_unweight]
        ring

theorem summable_norm_flowTerm (L γ δ t : ℝ) (y : L1 d) :
    Summable fun n => ‖flowTerm L γ δ t y n‖ :=
  summable_norm_of_tsum_enorm_ne_top (ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (tsum_enorm_flowTerm_le L γ δ t y))

/-- The vector field of the `a`-system in weighted `ℓ¹` coordinates. -/
@[expose] def flowField (L γ δ t : ℝ) (y : L1 d) : L1 d :=
  L1.mk (flowTerm L γ δ t y) (summable_norm_flowTerm L γ δ t y)

theorem flowField_apply (L γ δ t : ℝ) (y : L1 d) (n : Fin d → ℤ) :
    flowField L γ δ t y n = flowTerm L γ δ t y n := rfl

/-- `‖flowField t y‖ ≤ κ ‖y‖³`. -/
theorem norm_flowField_le (L γ δ t : ℝ) (y : L1 d) :
    ‖flowField L γ δ t y‖ ≤ |δ / (2 * L ^ ((d : ℝ) - γ))| * ‖y‖ ^ 3 := by
  rw [L1.norm_eq]
  refine tsum_norm_le_of_tsum_enorm_le (by positivity) ?_
  refine (tsum_enorm_flowTerm_le L γ δ t y).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]

/-- The local Lipschitz bound of the field. -/
theorem norm_flowField_sub_le (L γ δ t : ℝ) (y y' : L1 d) :
    ‖flowField L γ δ t y - flowField L γ δ t y'‖ ≤
      |δ / (2 * L ^ ((d : ℝ) - γ))| * (‖y‖ ^ 2 + ‖y‖ * ‖y'‖ + ‖y'‖ ^ 2) * ‖y - y'‖ := by
  set κ := |δ / (2 * L ^ ((d : ℝ) - γ))|
  set x := unweight (y : (Fin d → ℤ) → ℂ)
  set x' := unweight (y' : (Fin d → ℤ) → ℂ)
  have hx := summable_norm_unweight y
  have hx' := summable_norm_unweight y'
  have hdiff : unweight ((y - y' : L1 d) : (Fin d → ℤ) → ℂ) = x - x' := by
    funext n
    simp [x, x', unweight, sub_div]
  have hwd : wnorm (d + 1) (x - x') = ENNReal.ofReal ‖y - y'‖ := by
    rw [← hdiff, wnorm_unweight]
  have hc : ∀ z : (Fin d → ℤ) → ℂ, wnorm (d + 1) (fun m => (starRingEnd ℂ) (z m)) =
      wnorm (d + 1) z := fun z => by simp only [wnorm, ← ofReal_norm, Complex.norm_conj]
  rw [L1.norm_eq]
  refine tsum_norm_le_of_tsum_enorm_le (by positivity) ?_
  have hpt : ∀ n, ‖((flowField L γ δ t y - flowField L γ δ t y' : L1 d) : (Fin d → ℤ) → ℂ) n‖ₑ ≤
      ENNReal.ofReal κ * (wt (d + 1) n * tripleAbs (x - x') x x n +
        wt (d + 1) n * tripleAbs x' (x - x') x n + wt (d + 1) n * tripleAbs x' x' (x - x') n) := by
    intro n
    rw [lp.coeFn_sub, Pi.sub_apply, flowField_apply, flowField_apply, flowTerm, flowTerm, ← mul_sub,
      enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (flowWeight_pos n).le,
      ← wt_eq_ofReal_flowWeight]
    calc wt (d + 1) n * ‖aNonlin L γ δ 1 t x (fun m => (starRingEnd ℂ) (x m)) x n -
          aNonlin L γ δ 1 t x' (fun m => (starRingEnd ℂ) (x' m)) x' n‖ₑ
        ≤ wt (d + 1) n * (ENNReal.ofReal κ * (tripleAbs (x - x') x x n +
            tripleAbs x' (x - x') x n + tripleAbs x' x' (x - x') n)) := by
          gcongr
          exact enorm_aNonlin_sub_le L γ δ t hx hx' n
      _ = _ := by ring
  calc ∑' n, ‖((flowField L γ δ t y - flowField L γ δ t y' : L1 d) : (Fin d → ℤ) → ℂ) n‖ₑ
      ≤ ∑' n, ENNReal.ofReal κ * (wt (d + 1) n * tripleAbs (x - x') x x n +
          wt (d + 1) n * tripleAbs x' (x - x') x n + wt (d + 1) n * tripleAbs x' x' (x - x') n) :=
        ENNReal.tsum_le_tsum hpt
    _ ≤ ENNReal.ofReal κ * (wnorm (d + 1) (x - x') * wnorm (d + 1) x * wnorm (d + 1) x +
          wnorm (d + 1) x' * wnorm (d + 1) (x - x') * wnorm (d + 1) x +
          wnorm (d + 1) x' * wnorm (d + 1) x' * wnorm (d + 1) (x - x')) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add]
        gcongr
        · exact tsum_wt_mul_tripleAbs_le _ _ _ _
        · exact tsum_wt_mul_tripleAbs_le _ _ _ _
        · exact tsum_wt_mul_tripleAbs_le _ _ _ _
    _ = ENNReal.ofReal (κ * (‖y‖ ^ 2 + ‖y‖ * ‖y'‖ + ‖y'‖ ^ 2) * ‖y - y'‖) := by
        rw [hwd, wnorm_unweight y, wnorm_unweight y']
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (abs_nonneg _),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _)]
        ring

end WaveTurbulence.NLS
