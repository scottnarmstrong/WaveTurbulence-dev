/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Iterate
/-! # FL-POLAR: the bound for `(1 + |x|^2)^r · Phi` by induction on the rounds. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset LGSpine

variable {w d : ℕ}

theorem triple_sum_norm_le (a : ℕ → ℝ) (R : Finset ℕ) (F : Fin d → ℕ → ℕ → ℂ) (Y T1 : ℝ)
    (hY : 0 ≤ Y) (hT : ∑ m ∈ R, |a m| ≤ T1) (hF : ∀ i, ∀ m ∈ R, ∀ m' ∈ R, ‖F i m m'‖ ≤ Y) :
    ‖∑ i : Fin d, ∑ m ∈ R, ∑ m' ∈ R, ((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ ≤
      d * T1 ^ 2 * Y := by
  have hT0 : 0 ≤ T1 := (Finset.sum_nonneg fun m _ => abs_nonneg _).trans hT
  have h1 : ∀ i : Fin d, ‖∑ m ∈ R, ∑ m' ∈ R, ((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ ≤
      (∑ m ∈ R, |a m|) * (∑ m' ∈ R, |a m'|) * Y := by
    intro i
    calc _ ≤ ∑ m ∈ R, ‖∑ m' ∈ R, ((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ R, ∑ m' ∈ R, ‖((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ :=
          sum_le_sum fun m _ => norm_sum_le _ _
      _ ≤ ∑ m ∈ R, ∑ m' ∈ R, |a m| * |a m'| * Y := by
          refine sum_le_sum fun m hm => sum_le_sum fun m' hm' => ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hF i m hm m' hm') (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine sum_congr rfl fun m _ => ?_
          rw [Finset.sum_mul]
  calc _ ≤ ∑ i : Fin d, ‖∑ m ∈ R, ∑ m' ∈ R, ((a m : ℝ) : ℂ) * ((a m' : ℝ) : ℂ) * F i m m'‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (∑ m ∈ R, |a m|) * (∑ m' ∈ R, |a m'|) * Y := sum_le_sum fun i _ => h1 i
    _ = d * ((∑ m ∈ R, |a m|) * (∑ m' ∈ R, |a m'|)) * Y := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ d * (T1 * T1) * Y := by
        have hs : 0 ≤ ∑ m ∈ R, |a m| := Finset.sum_nonneg fun m _ => abs_nonneg _
        gcongr
    _ = _ := by ring

variable (P : WTParams) (hL : 1 ≤ P.L) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat)
  (dagger : Option (Fin w → Fin 3 → Mom P.d))
  (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (hW : ∀ LG k, |W LG k| ≤ 1)
  (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

end WaveTurbulence.Flower.Polar
