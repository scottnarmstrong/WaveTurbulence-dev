/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FamilyW.Scale
/-! # Single-scale version of `FamilyW.cut1_scale_bound_W`.

The filtered family hypothesis `FlowerFiltFamilyAt` is conditional on the cut1 index `j`
(`(2^j L)^10 ≤ ‖latticePoint n‖`), so the scale bound is needed for one `j` at a time.
This is `FamilyW.cut1_scale_bound_W` with the quantifier `∀ j` moved outside the family hypothesis
(the proof is the same case split `j = 0` / `j = r + 1`, which uses `H j` only). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Cases
open WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW

theorem cut1_scale_bound_W_at (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (S : ℕ) (C U J b c : ℝ)
    (hC : 0 < C) (hU : 0 < U) (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hδ1 : P.δ ≤ 1)
    (hν : 0 ≤ P.ν) (hJ : 0 ≤ J) (hc : 0 ≤ c)
    (hsmall : (4 * Real.exp 1) ^ (2 * w) * P.δ ^ (c * P.ν) ≤ 1)
    (hA : 4 * ((2 * N + 1 : ℕ) : ℝ) ≤ P.L)
    (hρ : C * ((2 * N + 1 : ℕ) : ℝ) * U * (4 * ((2 * N + 1 : ℕ) : ℝ)) ^ S ≤ P.L ^ S)
    (hcost : 3 * (4 * Real.exp 1) * 4 ^ S * C * U * ((2 * N + 1 : ℕ) : ℝ) ^ (S + 2) ≤ P.L)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (hW : ∀ LG k, |W LG k| ≤ 1) (j : ℕ)
    (H : UniformFlowerFamilyW P F p N kind pat dagger ζ t s n n' W
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => extractionRadius S N C U (2 ^ j * P.L))
      (J * P.L ^ (b - (S * w : ℕ) - (w : ℝ)) * P.δ ^ ((2 + c) * P.ν * N))) :
    ‖flowerWeighted P F p N kind pat dagger
        (fun LG k => W LG k * LG.cutWeight1P p P.L j k) ζ t s n n'‖ ≤
      J * P.L ^ b * P.δ ^ (2 * P.ν * N) * (2 ^ j * P.L) ^ (-((S * w : ℕ) : ℝ)) := by
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL
  have hD : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hM (j : ℕ) : P.L ≤ 2 ^ j * P.L :=
    le_mul_of_one_le_left hL0.le (one_le_pow₀ (by norm_num))
  have hcontrols (j : ℕ) := extraction_scale_controls S N hC hU hL0 (hM j) hA hρ
  have hmono : P.L ^ (b - (S * w : ℕ)) ≤ P.L ^ b :=
    Real.rpow_le_rpow_of_exponent_le hL (sub_le_self _ (by positivity))
  cases j with
  | zero =>
    have H0 := H
    simp only [pow_zero, one_mul] at H0
    have hz := Flower.FamilyW.cut1_zero_bound_of_familyW P F p N kind pat dagger ζ t s n n' W
      _ _ _ (by simpa only [pow_zero, one_mul] using (hcontrols 0).2) H0
    have he : P.L ^ (b - (S * w : ℕ) - (w : ℝ)) ≤ P.L ^ (b - (S * w : ℕ)) :=
      Real.rpow_le_rpow_of_exponent_le hL (sub_le_self _ (Nat.cast_nonneg _))
    have hcn : 0 ≤ c * P.ν * N := mul_nonneg (mul_nonneg hc hν) (Nat.cast_nonneg N)
    have hd : P.δ ^ ((2 + c) * P.ν * N) ≤ P.δ ^ (2 * P.ν * N) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
        have : (2 + c) * P.ν * N = 2 * P.ν * N + c * P.ν * N := by ring
        linarith)
    apply hz.trans
    calc
      _ ≤ J * P.L ^ (b - (S * w : ℕ)) * P.δ ^ (2 * P.ν * N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he hJ) hd (by positivity) (by positivity)
      _ = _ := by
        simp only [pow_zero, one_mul]
        rw [sub_eq_add_neg, Real.rpow_add hL0]
        ring
  | succ r =>
    have hc' := cut1_bound_of_familyW P F p N kind pat dagger ζ t s n n' W r
      _ _ _ hL0 (zero_lt_one.trans_le (hcontrols (r + 1)).1) (hcontrols (r + 1)).2
      (by positivity) (by
        have he : ((2 * N + 1 : ℕ) : ℝ) * ((2 ^ (r + 1) * P.L) / (4 * (2 * N + 1 : ℕ))) =
          (2 ^ (r + 1) * P.L) / 4 := by field_simp
        exact he.le) hF hW H
    have ha := extraction_absorption_c S N w hC hU hL0 (hL0.trans_le (hM (r + 1))) hδ hJ hsmall hcost
      (b := b - (S * w : ℕ) - (w : ℝ))
    apply hc'.trans (ha.trans ?_)
    have he : b - ((S * w : ℕ) : ℝ) - (w : ℝ) + (w : ℝ) = b - (S * w : ℕ) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hJ) (by positivity)) (by positivity)

end WaveTurbulence.Flower.Cases
