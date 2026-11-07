/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FamilyW.Extraction
public import WaveTurbulence.Foundations.FC23.Cut1ScaleBound
/-! The numerical cut1 scale estimate for the `W`-weighted family, with a free `δ`-exponent `c`
(`c = 6` recovers main's `FC23.cut1_scale_bound`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.FamilyW
open WaveTurbulence.FC23

theorem interpolation_delta_absorption_c {δ ν E c : ℝ} (hδ : 0 < δ) (hE : 0 ≤ E)
    (w N : ℕ) (hsmall : E ^ (2 * w) * δ ^ (c * ν) ≤ 1) :
    E ^ (w * (2 * N + 1)) * δ ^ ((2 + c) * ν * N) ≤ E ^ w * δ ^ (2 * ν * N) := by
  have hpow := pow_le_one₀ (mul_nonneg (pow_nonneg hE _) (Real.rpow_nonneg hδ.le _)) hsmall (n := N)
  have hsplit : E ^ (w * (2 * N + 1)) * δ ^ ((2 + c) * ν * N) =
      E ^ w * (E ^ (2 * w) * δ ^ (c * ν)) ^ N * δ ^ (2 * ν * N) := by
    rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
    have he : w + 2 * w * N = w * (2 * N + 1) := by ring
    rw [he, ← Real.rpow_mul_natCast hδ.le]
    simp only [mul_assoc]
    rw [← Real.rpow_add hδ]
    congr 2
    ring
  rw [hsplit]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (pow_nonneg hE _))
    (Real.rpow_nonneg hδ.le _)).trans_eq (by ring)

theorem extraction_absorption_c (S N w : ℕ) {C U L M δ ν J b c : ℝ}
    (hC : 0 < C) (hU : 0 < U) (hL : 0 < L) (hM : 0 < M) (hδ : 0 < δ) (hJ : 0 ≤ J)
    (hsmall : (4 * Real.exp 1) ^ (2 * w) * δ ^ (c * ν) ≤ 1)
    (hcost : 3 * (4 * Real.exp 1) * 4 ^ S * C * U * ((2 * N + 1 : ℕ) : ℝ) ^ (S + 2) ≤ L) :
    (3 : ℝ) ^ w * (4 * Real.exp 1) ^ (w * (2 * N + 1)) *
      (((2 * N + 1 : ℕ) : ℝ) / extractionRadius S N C U M) ^ w *
      (J * L ^ b * δ ^ ((2 + c) * ν * N)) ≤
      J * L ^ (b + (w : ℝ)) * δ ^ (2 * ν * N) * M ^ (-((S * w : ℕ) : ℝ)) := by
  let E : ℝ := 4 * Real.exp 1
  let t : ℝ := ((2 * N + 1 : ℕ) : ℝ) / extractionRadius S N C U M
  have ht : 0 ≤ t := div_nonneg (by positivity) (extractionRadius_pos S N hC hU hM).le
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hnum : 3 * E * t ≤ L / M ^ S := by
    dsimp only [t, E]
    rw [extractionRadius_identity S N hC hU hM]
    calc
      _ = (3 * (4 * Real.exp 1) * 4 ^ S * C * U * ((2 * N + 1 : ℕ) : ℝ) ^ (S + 2)) / M ^ S := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hcost (pow_nonneg hM.le S)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * E * t) hnum w
  have hδabs := interpolation_delta_absorption_c hδ hE w N hsmall
  calc
    _ = (3 ^ w * t ^ w * (J * L ^ b)) * (E ^ (w * (2 * N + 1)) * δ ^ ((2 + c) * ν * N)) := by
      dsimp [t, E]; ring
    _ ≤ (3 ^ w * t ^ w * (J * L ^ b)) * (E ^ w * δ ^ (2 * ν * N)) :=
      mul_le_mul_of_nonneg_left hδabs (by positivity)
    _ = (3 * E * t) ^ w * (J * L ^ b * δ ^ (2 * ν * N)) := by dsimp only [E]; simp only [mul_pow]; ring
    _ ≤ (L / M ^ S) ^ w * (J * L ^ b * δ ^ (2 * ν * N)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      rw [div_pow, ← pow_mul, Real.rpow_neg hM.le, Real.rpow_natCast,
        Real.rpow_add hL, Real.rpow_natCast]
      ring

theorem cut1_scale_bound_W (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
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
    (hW : ∀ LG k, |W LG k| ≤ 1)
    (H : ∀ j : ℕ, UniformFlowerFamilyW P F p N kind pat dagger ζ t s n n' W
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => extractionRadius S N C U (2 ^ j * P.L))
      (J * P.L ^ (b - (S * w : ℕ) - (w : ℝ)) * P.δ ^ ((2 + c) * P.ν * N))) :
    ∀ j : ℕ, ‖flowerWeighted P F p N kind pat dagger
        (fun LG k => W LG k * LG.cutWeight1P p P.L j k) ζ t s n n'‖ ≤
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
        exact he.le) hF hW (H (r + 1))
    have ha := extraction_absorption_c S N w hC hU hL0 (hL0.trans_le (hM (r + 1))) hδ hJ hsmall hcost
      (b := b - (S * w : ℕ) - (w : ℝ))
    apply hc'.trans (ha.trans ?_)
    have he : b - ((S * w : ℕ) : ℝ) - (w : ℝ) + (w : ℝ) = b - (S * w : ℕ) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hJ) (by positivity)) (by positivity)
end WaveTurbulence.Flower.FamilyW
