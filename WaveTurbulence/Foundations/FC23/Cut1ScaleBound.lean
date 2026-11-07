/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.ExtractionAbsorption
/-! The complete numerical cut1 estimate, including the j1=0 endpoint. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.FC23

theorem cut1_scale_bound (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (S : ℕ) (C U J b : ℝ)
    (hC : 0 < C) (hU : 0 < U) (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hδ1 : P.δ ≤ 1)
    (hν : 0 ≤ P.ν) (hJ : 0 ≤ J)
    (hsmall : (4 * Real.exp 1) ^ (2 * w) * P.δ ^ (6 * P.ν) ≤ 1)
    (hA : 4 * ((2 * N + 1 : ℕ) : ℝ) ≤ P.L)
    (hρ : C * ((2 * N + 1 : ℕ) : ℝ) * U * (4 * ((2 * N + 1 : ℕ) : ℝ)) ^ S ≤ P.L ^ S)
    (hcost : 3 * (4 * Real.exp 1) * 4 ^ S * C * U * ((2 * N + 1 : ℕ) : ℝ) ^ (S + 2) ≤ P.L)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (H : ∀ j : ℕ, FC23UniformFlowerFamily P F p N kind pat dagger ζ t s n n'
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => extractionRadius S N C U (2 ^ j * P.L))
      (J * P.L ^ (b - (S * w : ℕ) - (w : ℝ)) * P.δ ^ (8 * P.ν * N))) :
    ∀ j : ℕ, ‖flowerSumP P F p N kind pat dagger (some j) none ζ t s n n'‖ ≤
      J * P.L ^ b * P.δ ^ (2 * P.ν * N) * (2 ^ j * P.L) ^ (-((S * w : ℕ) : ℝ)) := by
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL
  have hD : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hM (j : ℕ) : P.L ≤ 2 ^ j * P.L :=
    le_mul_of_one_le_left hL0.le (one_le_pow₀ (by norm_num))
  have hcontrols (j : ℕ) := extraction_scale_controls S N hC hU hL0 (hM j) hA hρ
  have hmono : P.L ^ (b - (S * w : ℕ)) ≤ P.L ^ b :=
    Real.rpow_le_rpow_of_exponent_le hL (sub_le_self _ (by positivity))
  intro j
  cases j with
  | zero =>
    have H0 := H 0
    simp only [pow_zero, one_mul] at H0
    have hc := cut1_zero_bound_of_uniformFlowerFamily P F p N kind pat dagger ζ t s n n'
      _ _ _ (by simpa only [pow_zero, one_mul] using (hcontrols 0).2) H0
    have he : P.L ^ (b - (S * w : ℕ) - (w : ℝ)) ≤ P.L ^ (b - (S * w : ℕ)) :=
      Real.rpow_le_rpow_of_exponent_le hL (sub_le_self _ (Nat.cast_nonneg _))
    have hd : P.δ ^ (8 * P.ν * N) ≤ P.δ ^ (2 * P.ν * N) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
    apply hc.trans
    calc
      _ ≤ J * P.L ^ (b - (S * w : ℕ)) * P.δ ^ (2 * P.ν * N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he hJ) hd (by positivity) (by positivity)
      _ = _ := by
        simp only [pow_zero, one_mul]
        rw [sub_eq_add_neg, Real.rpow_add hL0]
        ring
  | succ r =>
    have hc := cut1_bound_of_uniformFlowerFamily P F p N kind pat dagger ζ t s n n' r
      _ _ _ hL0 (zero_lt_one.trans_le (hcontrols (r + 1)).1) (hcontrols (r + 1)).2
      (by positivity) (by
        have he : ((2 * N + 1 : ℕ) : ℝ) * ((2 ^ (r + 1) * P.L) / (4 * (2 * N + 1 : ℕ))) =
          (2 ^ (r + 1) * P.L) / 4 := by field_simp
        exact he.le) hF (H (r + 1))
    have ha := extraction_absorption S N w hC hU hL0 (hL0.trans_le (hM (r + 1))) hδ hJ hsmall hcost
      (b := b - (S * w : ℕ) - (w : ℝ))
    apply hc.trans (ha.trans ?_)
    have he : b - ((S * w : ℕ) : ℝ) - (w : ℝ) + (w : ℝ) = b - (S * w : ℕ) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hJ) (by positivity)) (by positivity)
end WaveTurbulence.FC23
