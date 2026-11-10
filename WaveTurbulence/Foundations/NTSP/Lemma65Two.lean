/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Lemma65Pointwise

/-!
# DH23 Lemma 6.5 (2)

The `s`-integral of the nonzero Poisson modes, for `Φ` supported in `|s| ≤ κL`, `d ≥ 3`,
`1 ≤ λ ≤ L^η`, `0 ≤ η ≤ 1/20`, split at `|s| = L^{5/6}`:

* `|s| > L^{5/6}`: the full sum is `≲ λ^{2d+2} ⟨s⟩^{-d}`, and
  `λ^{2d+2} ∫_{|s| > L^{5/6}} ⟨s⟩^{-d} ds ≲ L^{2η(d+1) - (5/6)(d - 5/4)} ≤ L^{-1}`;
* `|s| ≤ L^{5/6}` (and `L^{7/60} ≥ 8√d`, so that `λ√d|s| ≤ L/8`): the far modes give
  `λ^{2d+2} L^{5/3 - (d+1)} ≤ L^{-1}`, the near modes `(λ + 1)/L + 1_{|ξ| > L/2} + 1_{|ζ| > L/2}`;
* small `L` (`L^{7/60} < 8√d`): the full sum, with a constant.

This gives `lintegral_nonzeroModes_le`, and from it the statement of DH23 L1025–L1031 (`ntsp_two`)
and the uniform bound for the full sum (`ntsp_two_all`, DH23 L1032–L1035).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-! ### Real arithmetic -/

theorem pow_le_rpow_of_le {L lam η : ℝ} (hL : 1 ≤ L) (hlam : 1 ≤ lam) (hle : lam ≤ L ^ η)
    (n : ℕ) : lam ^ n ≤ L ^ (η * n) := by
  rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
  exact pow_le_pow_left₀ (by linarith) hle n

/-- `∫_ℝ ⟨s⟩^{-5/4} ds`. -/
@[expose] def tailInt : ℝ := ∫ s : ℝ, (1 + |s|) ^ (-(5 / 4 : ℝ))

theorem integrable_tail : Integrable (fun s : ℝ => (1 + |s|) ^ (-(5 / 4 : ℝ))) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5 / 4)
    (by rw [Module.finrank_self]; norm_num)
  simpa only [Real.norm_eq_abs] using h

theorem tailInt_nonneg : 0 ≤ tailInt := integral_nonneg fun _ => by positivity

/-- The tail `∫_{|s| > R} ⟨s⟩^{-d}` is at most `R^{-(d - 5/4)} ∫ ⟨s⟩^{-5/4}`. -/
theorem lintegral_tail_le (hd : 2 ≤ d) {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R) :
    ∫⁻ s, {s : ℝ | R < |s|}.indicator (fun s => ENNReal.ofReal (A * ((1 + |s|) ^ d)⁻¹)) s ≤
      ENNReal.ofReal (A * R ^ (-((d : ℝ) - 5 / 4)) * tailInt) := by
  have hpt : ∀ s, {s : ℝ | R < |s|}.indicator (fun s => ENNReal.ofReal (A * ((1 + |s|) ^ d)⁻¹)) s ≤
      ENNReal.ofReal (A * R ^ (-((d : ℝ) - 5 / 4)) * (1 + |s|) ^ (-(5 / 4 : ℝ))) := fun s => by
    by_cases hs : s ∈ {s : ℝ | R < |s|}
    · rw [Set.indicator_of_mem hs]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hA
      have hS : R ≤ 1 + |s| := by have : R < |s| := hs; linarith
      have h1 : ((1 + |s|) ^ d)⁻¹ = (1 + |s|) ^ (-((d : ℝ) - 5 / 4)) * (1 + |s|) ^ (-(5 / 4 : ℝ)) := by
        rw [← Real.rpow_add (by positivity), show -((d : ℝ) - 5 / 4) + -(5 / 4) = -(d : ℝ) by ring,
          Real.rpow_neg (by positivity), Real.rpow_natCast]
      rw [h1]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hS
        (by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
            linarith)
    · rw [Set.indicator_of_notMem hs]; exact bot_le
  calc ∫⁻ s, {s : ℝ | R < |s|}.indicator (fun s => ENNReal.ofReal (A * ((1 + |s|) ^ d)⁻¹)) s
      ≤ ∫⁻ s, ENNReal.ofReal (A * R ^ (-((d : ℝ) - 5 / 4)) * (1 + |s|) ^ (-(5 / 4 : ℝ))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (∫ s, A * R ^ (-((d : ℝ) - 5 / 4)) * (1 + |s|) ^ (-(5 / 4 : ℝ))) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_tail.const_mul _)
          (Filter.Eventually.of_forall fun s => by positivity)).symm
    _ = _ := by rw [integral_const_mul, tailInt]

/-- `∫_{|s| ≤ R} (1 + |s|) ds ≤ 4R²` for `R ≥ 1`. -/
theorem lintegral_le_R_le {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R) :
    ∫⁻ s, {s : ℝ | |s| ≤ R}.indicator (fun s => ENNReal.ofReal (A * (1 + |s|))) s ≤
      ENNReal.ofReal (A * (4 * R ^ 2)) := by
  have hpt : ∀ s, {s : ℝ | |s| ≤ R}.indicator (fun s => ENNReal.ofReal (A * (1 + |s|))) s ≤
      (Icc (-R) R).indicator (fun _ => ENNReal.ofReal (A * (2 * R))) s := fun s => by
    by_cases hs : |s| ≤ R
    · rw [Set.indicator_of_mem (show s ∈ {s : ℝ | |s| ≤ R} from hs),
        Set.indicator_of_mem (show s ∈ Icc (-R) R from abs_le.1 hs)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) hA)
    · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ | |s| ≤ R} from hs)]; exact bot_le
  calc _ ≤ ∫⁻ s, (Icc (-R) R).indicator (fun _ => ENNReal.ofReal (A * (2 * R))) s :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (A * (2 * R)) * volume (Icc (-R) R) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (A * (4 * R ^ 2)) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

section Exponents

variable {L lam η : ℝ}

theorem exp_regionI (hd : 3 ≤ d) (hL : 1 ≤ L) (hlam : 1 ≤ lam) (hle : lam ≤ L ^ η)
    (hη : η ≤ 1 / 20) :
    lam ^ (2 * (d + 1)) * (L ^ (5 / 6 : ℝ)) ^ (-((d : ℝ) - 5 / 4)) ≤ L ^ (-1 + η) := by
  have hL0 : 0 < L := by linarith
  have h1 := pow_le_rpow_of_le hL hlam hle (2 * (d + 1))
  rw [← Real.rpow_mul hL0.le]
  calc lam ^ (2 * (d + 1)) * L ^ (5 / 6 * -((d : ℝ) - 5 / 4))
      ≤ L ^ (η * ((2 * (d + 1) : ℕ) : ℝ)) * L ^ (5 / 6 * -((d : ℝ) - 5 / 4)) := by gcongr
    _ = L ^ (η * ((2 * (d + 1) : ℕ) : ℝ) + 5 / 6 * -((d : ℝ) - 5 / 4)) :=
        (Real.rpow_add hL0 _ _).symm
    _ ≤ L ^ (-1 + η) := by
        refine Real.rpow_le_rpow_of_exponent_le hL ?_
        have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
        push_cast
        nlinarith

theorem exp_far (hd : 3 ≤ d) (hL : 1 ≤ L) (hlam : 1 ≤ lam) (hle : lam ≤ L ^ η)
    (hη : η ≤ 1 / 20) :
    lam ^ (2 * (d + 1)) * (4 * (L ^ (5 / 6 : ℝ)) ^ 2) / L ^ (d + 1) ≤ 4 * L ^ (-1 + η) := by
  have hL0 : 0 < L := by linarith
  have h1 := pow_le_rpow_of_le hL hlam hle (2 * (d + 1))
  rw [div_le_iff₀ (by positivity)]
  have e1 : (L ^ (5 / 6 : ℝ)) ^ 2 = L ^ (5 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have e2 : L ^ (-1 + η) * L ^ (d + 1) = L ^ (-1 + η + ((d + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast L (d + 1), ← Real.rpow_add hL0]
  rw [e1]
  calc lam ^ (2 * (d + 1)) * (4 * L ^ (5 / 3 : ℝ))
      ≤ L ^ (η * ((2 * (d + 1) : ℕ) : ℝ)) * (4 * L ^ (5 / 3 : ℝ)) := by gcongr
    _ = 4 * L ^ (η * ((2 * (d + 1) : ℕ) : ℝ) + 5 / 3) := by
        rw [Real.rpow_add hL0]; ring
    _ ≤ 4 * L ^ (-1 + η + ((d + 1 : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL ?_) (by norm_num)
        have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
        push_cast
        nlinarith
    _ = 4 * L ^ (-1 + η) * L ^ (d + 1) := by rw [mul_assoc, e2]

theorem exp_near (hL : 1 ≤ L) (hlam : 1 ≤ lam) (hle : lam ≤ L ^ η) :
    (lam + 1) / L ≤ 2 * L ^ (-1 + η) := by
  have hL0 : 0 < L := by linarith
  rw [div_le_iff₀ hL0, show (-1 + η) = η - 1 by ring, Real.rpow_sub_one hL0.ne']
  field_simp
  linarith

theorem exp_rho (hL : 1 ≤ L) (hlam : 0 ≤ lam) (hle : lam ≤ L ^ η) (hη : η ≤ 1 / 20)
    (hbig : 8 * Real.sqrt d ≤ L ^ (7 / 60 : ℝ)) {s : ℝ} (hs : |s| ≤ L ^ (5 / 6 : ℝ)) :
    |s| * (lam * Real.sqrt d) ≤ L / 8 := by
  have hL0 : 0 < L := by linarith
  have h1 : lam ≤ L ^ (1 / 20 : ℝ) := hle.trans (Real.rpow_le_rpow_of_exponent_le hL hη)
  have hsd := Real.sqrt_nonneg d
  calc |s| * (lam * Real.sqrt d) ≤ L ^ (5 / 6 : ℝ) * (L ^ (1 / 20 : ℝ) * Real.sqrt d) := by
        gcongr
    _ = L ^ (53 / 60 : ℝ) * Real.sqrt d := by
        rw [← mul_assoc, ← Real.rpow_add hL0]; norm_num
    _ ≤ L ^ (53 / 60 : ℝ) * (L ^ (7 / 60 : ℝ) / 8) := by gcongr; linarith
    _ = L / 8 := by
        rw [mul_div_assoc', ← Real.rpow_add hL0]; norm_num

theorem exp_small (hL : 1 ≤ L) (hlam : 1 ≤ lam) (hle : lam ≤ L ^ η)
    (hη : η ≤ 1 / 20) (hsmall : L ^ (7 / 60 : ℝ) < 8 * Real.sqrt d) :
    lam ^ (2 * (d + 1)) ≤ ((8 * Real.sqrt d) ^ (60 / 7 : ℝ)) ^ (((d : ℝ) + 1) / 10 + 1) *
      L ^ (-1 + η) := by
  have hL0 : 0 < L := by linarith
  have hLL : L ≤ (8 * Real.sqrt d) ^ (60 / 7 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hsmall.le (by norm_num : (0 : ℝ) ≤ 60 / 7)
    rwa [← Real.rpow_mul hL0.le, show (7 / 60 : ℝ) * (60 / 7) = 1 by norm_num,
      Real.rpow_one] at h
  have h1 := pow_le_rpow_of_le hL hlam hle (2 * (d + 1))
  have h2 : L ^ (η * ((2 * (d + 1) : ℕ) : ℝ)) * L ^ (1 - η) ≤ L ^ (((d : ℝ) + 1) / 10 + 1) := by
    rw [← Real.rpow_add hL0]
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    push_cast
    nlinarith
  have h3 : L ^ (((d : ℝ) + 1) / 10 + 1) ≤
      ((8 * Real.sqrt d) ^ (60 / 7 : ℝ)) ^ (((d : ℝ) + 1) / 10 + 1) :=
    Real.rpow_le_rpow hL0.le hLL (by positivity)
  have h4 : L ^ (1 - η) * L ^ (-1 + η) = 1 := by
    rw [← Real.rpow_add hL0]; norm_num
  calc lam ^ (2 * (d + 1)) ≤ L ^ (η * ((2 * (d + 1) : ℕ) : ℝ)) := h1
    _ = L ^ (η * ((2 * (d + 1) : ℕ) : ℝ)) * L ^ (1 - η) * L ^ (-1 + η) := by
        rw [mul_assoc, h4, mul_one]
    _ ≤ _ := by gcongr; exact h2.trans h3

end Exponents

theorem measurable_nearSum (d N : ℕ) (L lam : ℝ) (c v : Mom d) :
    Measurable (fun s => nearSum d N L lam s c v) := by
  unfold nearSum
  refine Measurable.tsum fun g => ?_
  have h : (fun s => {g : Fin d → ℤ | g ≠ 0 ∧ ‖(L • intVec g + c) + s • v‖ < L / 4}.indicator
      (fun g => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
        (decayW N (‖(L • intVec g + c) + s • v‖ - |s| * (lam * Real.sqrt d))))) g) =
      {s : ℝ | g ≠ 0 ∧ ‖(L • intVec g + c) + s • v‖ < L / 4}.indicator
      (fun s => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
        (decayW N (‖(L • intVec g + c) + s • v‖ - |s| * (lam * Real.sqrt d))))) := by
    funext s
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [h]
  refine Measurable.indicator (ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)) ?_
  · exact Continuous.min (Continuous.inv₀ (by fun_prop) (fun s => by positivity))
      ((continuous_decayW N).comp (by fun_prop))
  · have hm : Measurable fun s : ℝ => ‖(L • intVec g + c) + s • v‖ := by fun_prop
    exact (MeasurableSet.const (g ≠ 0)).inter (measurableSet_lt hm measurable_const)

/-- The constant of the integrated mode sums. -/
@[expose] def modeConst (d : ℕ) (κ : ℝ) : ℝ :=
  fullConst d κ * tailInt + 8 * farConst d κ + 4 * nearConst d + sInt d +
    fullConst d κ * sInt d * ((8 * Real.sqrt d) ^ (60 / 7 : ℝ)) ^ (((d : ℝ) + 1) / 10 + 1)

theorem modeConst_nonneg (d : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ modeConst d κ := by
  unfold modeConst
  have := fullConst_nonneg d hκ; have := farConst_nonneg d hκ; have := nearConst_nonneg d
  have := sInt_nonneg d; have := tailInt_nonneg
  positivity

/-- **The integrated mode sums**: for `|s| ≤ κL`, `d ≥ 3`, `1 ≤ λ ≤ L^η`, `η ≤ 1/20`,
`∫_{|s| ≤ κL} T(s) ds ≤ C (L^{-1+η} + 1_{|ξ| > L/2} + 1_{|ζ| > L/2})`. -/
theorem lintegral_modeSum_le (hd : 3 ≤ d) {κ η L lam : ℝ} (hκ : 0 < κ) (hη : η ≤ 1 / 20)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (hle : lam ≤ L ^ η) (a b ξ ζ : Mom d) :
    ∫⁻ s, {s : ℝ | |s| ≤ κ * L}.indicator (fun s => modeSum d (10 * d) L lam s a b ξ ζ) s ≤
      ENNReal.ofReal (modeConst d κ * (L ^ (-1 + η) +
        {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ξ +
        {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ζ)) := by
  set N := 10 * d
  set L₀ : ℝ := (8 * Real.sqrt d) ^ (60 / 7 : ℝ)
  set e : ℝ := ((d : ℝ) + 1) / 10 + 1
  set C₁ := modeConst d κ
  have hC₁def : C₁ = fullConst d κ * tailInt + 8 * farConst d κ + 4 * nearConst d + sInt d +
      fullConst d κ * sInt d * L₀ ^ e := rfl
  have hF := fullConst_nonneg d hκ.le
  have hFa := farConst_nonneg d hκ.le
  have hNe := nearConst_nonneg d
  have hS := sInt_nonneg d
  have hT := tailInt_nonneg
  have hC₁ : 0 ≤ C₁ := modeConst_nonneg d hκ.le
  have hL0 : 0 < L := by linarith
  set iξ : ℝ := {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ξ
  set iζ : ℝ := {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ζ
  have hiξ : 0 ≤ iξ := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hiζ : 0 ≤ iζ := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  set M : ℝ → ℝ≥0∞ := fun s => {s : ℝ | |s| ≤ κ * L}.indicator
    (fun s => modeSum d N L lam s a b ξ ζ) s
  show ∫⁻ s, M s ≤ ENNReal.ofReal (C₁ * (L ^ (-1 + η) + iξ + iζ))
  have hLη : 0 ≤ L ^ (-1 + η) := by positivity
  by_cases hbig : 8 * Real.sqrt d ≤ L ^ (7 / 60 : ℝ)
  · set R : ℝ := L ^ (5 / 6 : ℝ)
    have hR : 1 ≤ R := Real.one_le_rpow hL (by norm_num)
    set A := fullConst d κ * lam ^ (2 * (d + 1))
    have hA : 0 ≤ A := by have : 0 ≤ lam := by linarith
                          positivity
    set B := 2 * (farConst d κ * lam ^ (2 * (d + 1)) / L ^ (d + 1))
    have hB : 0 ≤ B := by have : 0 ≤ lam := by linarith
                          positivity
    set f1 : ℝ → ℝ≥0∞ := fun s => {s : ℝ | R < |s|}.indicator
      (fun s => ENNReal.ofReal (A * ((1 + |s|) ^ d)⁻¹)) s
    set f2 : ℝ → ℝ≥0∞ := fun s => {s : ℝ | |s| ≤ R}.indicator
      (fun s => ENNReal.ofReal (B * (1 + |s|))) s
    set f3 : ℝ → ℝ≥0∞ := fun s => nearSum d N L lam s ξ b + nearSum d N L lam s ζ a
    have hpt : ∀ s, M s ≤ f1 s + f2 s + f3 s := fun s => by
      by_cases hs : |s| ≤ κ * L
      · simp only [M, Set.indicator_of_mem (show s ∈ {s : ℝ | |s| ≤ κ * L} from hs)]
        by_cases hR' : R < |s|
        · refine le_trans ?_ (le_self_add.trans le_self_add)
          simp only [f1, Set.indicator_of_mem (show s ∈ {s : ℝ | R < |s|} from hR')]
          exact modeSum_le_full (by omega) hL hκ.le hs hlam a b ξ ζ
        · have hsR : |s| ≤ R := not_lt.1 hR'
          have hρ := exp_rho hL (by linarith) hle hη hbig hsR
          refine (modeSum_le_split (by omega) hL hκ.le hs hlam hρ a b ξ ζ).trans ?_
          simp only [f2, f3, Set.indicator_of_mem (show s ∈ {s : ℝ | |s| ≤ R} from hsR)]
          have h2 : 2 * ENNReal.ofReal (farConst d κ * lam ^ (2 * (d + 1)) * (1 + |s|) /
              L ^ (d + 1)) = ENNReal.ofReal (B * (1 + |s|)) := by
            rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            simp only [B]; ring
          rw [h2, add_assoc]
          exact le_add_self
      · simp only [M, Set.indicator_of_notMem (show s ∉ {s : ℝ | |s| ≤ κ * L} from hs)]
        exact bot_le
    have hc1 : Continuous fun s : ℝ => A * ((1 + |s|) ^ d)⁻¹ :=
      continuous_const.mul (Continuous.inv₀ (by fun_prop) (fun s => by positivity))
    have hf1m : Measurable f1 := (ENNReal.measurable_ofReal.comp hc1.measurable).indicator
      (measurableSet_lt measurable_const (by fun_prop))
    have hf2m : Measurable f2 :=
      (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun s : ℝ => B * (1 + |s|))).indicator
        (measurableSet_le (by fun_prop) measurable_const)
    have h1 : ∫⁻ s, f1 s ≤ ENNReal.ofReal (A * R ^ (-((d : ℝ) - 5 / 4)) * tailInt) :=
      lintegral_tail_le (by omega) hA hR
    have h2 : ∫⁻ s, f2 s ≤ ENNReal.ofReal (B * (4 * R ^ 2)) := lintegral_le_R_le hB hR
    have hind : ∀ x : Mom d, {x : Mom d | L / 2 < ‖x‖}.indicator
        (fun _ => ENNReal.ofReal (sInt d)) x =
        ENNReal.ofReal (sInt d * {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) x) := fun x => by
      by_cases hx : x ∈ {x : Mom d | L / 2 < ‖x‖}
      · simp only [Set.indicator_of_mem hx, mul_one]
      · simp only [Set.indicator_of_notMem hx, mul_zero, ENNReal.ofReal_zero]
    have h3 : ∫⁻ s, f3 s ≤ ENNReal.ofReal (2 * (nearConst d * (lam + 1) / L) +
        sInt d * (iξ + iζ)) := by
      simp only [f3]
      rw [lintegral_add_left (measurable_nearSum d N L lam ξ b)]
      refine (add_le_add (lintegral_nearModes_le hd (by omega) hL0 (by linarith) ξ b)
        (lintegral_nearModes_le hd (by omega) hL0 (by linarith) ζ a)).trans (le_of_eq ?_)
      rw [hind, hind, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simp only [iξ, iζ]
      ring
    have hI := exp_regionI hd hL hlam hle hη
    have hFr := exp_far hd hL hlam hle hη
    have hNr := exp_near hL hlam hle
    calc ∫⁻ s, M s ≤ ∫⁻ s, (f1 s + f2 s + f3 s) := lintegral_mono hpt
      _ = (∫⁻ s, f1 s) + (∫⁻ s, f2 s) + ∫⁻ s, f3 s := by
          rw [lintegral_add_left (f := fun s => f1 s + f2 s) (hf1m.add hf2m),
            lintegral_add_left hf1m]
      _ ≤ ENNReal.ofReal (A * R ^ (-((d : ℝ) - 5 / 4)) * tailInt) +
            ENNReal.ofReal (B * (4 * R ^ 2)) +
            ENNReal.ofReal (2 * (nearConst d * (lam + 1) / L) + sInt d * (iξ + iζ)) :=
          add_le_add (add_le_add h1 h2) h3
      _ = ENNReal.ofReal (A * R ^ (-((d : ℝ) - 5 / 4)) * tailInt + B * (4 * R ^ 2) +
            (2 * (nearConst d * (lam + 1) / L) + sInt d * (iξ + iζ))) := by
          rw [ENNReal.ofReal_add (p := A * R ^ (-((d : ℝ) - 5 / 4)) * tailInt + B * (4 * R ^ 2))
            (by positivity) (by positivity),
            ENNReal.ofReal_add (p := A * R ^ (-((d : ℝ) - 5 / 4)) * tailInt)
            (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (C₁ * (L ^ (-1 + η) + iξ + iζ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e1 : A * R ^ (-((d : ℝ) - 5 / 4)) * tailInt =
              fullConst d κ * tailInt * (lam ^ (2 * (d + 1)) * R ^ (-((d : ℝ) - 5 / 4))) := by
            simp only [A]; ring
          have e2 : B * (4 * R ^ 2) =
              2 * farConst d κ * (lam ^ (2 * (d + 1)) * (4 * R ^ 2) / L ^ (d + 1)) := by
            simp only [B]; ring
          rw [e1, e2]
          have k1 : fullConst d κ * tailInt * (lam ^ (2 * (d + 1)) * R ^ (-((d : ℝ) - 5 / 4))) ≤
              fullConst d κ * tailInt * L ^ (-1 + η) :=
            mul_le_mul_of_nonneg_left hI (by positivity)
          have k2 : 2 * farConst d κ * (lam ^ (2 * (d + 1)) * (4 * R ^ 2) / L ^ (d + 1)) ≤
              2 * farConst d κ * (4 * L ^ (-1 + η)) :=
            mul_le_mul_of_nonneg_left hFr (by positivity)
          have k3 : 2 * (nearConst d * (lam + 1) / L) ≤ 2 * (nearConst d * (2 * L ^ (-1 + η))) := by
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNr hNe) (by norm_num)
          have k4 : fullConst d κ * sInt d * L₀ ^ e * L ^ (-1 + η) ≥ 0 := by positivity
          have k5 : sInt d * (iξ + iζ) ≤ C₁ * (iξ + iζ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [hC₁def]
            have : 0 ≤ fullConst d κ * sInt d * L₀ ^ e := by positivity
            have h1 : 0 ≤ fullConst d κ * tailInt := mul_nonneg hF hT
            linarith only [this, h1, hFa, hNe]
          have hC₁L : C₁ * L ^ (-1 + η) = (fullConst d κ * tailInt + 8 * farConst d κ + 4 * nearConst d +
              sInt d + fullConst d κ * sInt d * L₀ ^ e) * L ^ (-1 + η) := by rw [hC₁def]
          have hSL : 0 ≤ sInt d * L ^ (-1 + η) := mul_nonneg hS hLη
          linarith only [k1, k2, k3, k4, k5, hC₁L, hSL]
  · -- small `L`
    have hsmall : L ^ (7 / 60 : ℝ) < 8 * Real.sqrt d := not_le.1 hbig
    set A := fullConst d κ * lam ^ (2 * (d + 1))
    have hA : 0 ≤ A := by have : 0 ≤ lam := by linarith
                          positivity
    have hpt : ∀ s, M s ≤ ENNReal.ofReal (A * ((1 + |s|) ^ d)⁻¹) := fun s => by
      by_cases hs : |s| ≤ κ * L
      · simp only [M, Set.indicator_of_mem (show s ∈ {s : ℝ | |s| ≤ κ * L} from hs)]
        exact modeSum_le_full (by omega) hL hκ.le hs hlam a b ξ ζ
      · simp only [M, Set.indicator_of_notMem (show s ∉ {s : ℝ | |s| ≤ κ * L} from hs)]
        exact bot_le
    refine (lintegral_le_of_le_inv_pow (by omega) hA hpt).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsm := exp_small hL hlam hle hη hsmall
    have k1 : A * sInt d ≤ fullConst d κ * sInt d * L₀ ^ e * L ^ (-1 + η) := by
      simp only [A]
      calc fullConst d κ * lam ^ (2 * (d + 1)) * sInt d =
          fullConst d κ * sInt d * lam ^ (2 * (d + 1)) := by ring
        _ ≤ fullConst d κ * sInt d * (L₀ ^ e * L ^ (-1 + η)) :=
            mul_le_mul_of_nonneg_left hsm (by positivity)
        _ = _ := by ring
    have k2 : fullConst d κ * sInt d * L₀ ^ e * L ^ (-1 + η) ≤ C₁ * L ^ (-1 + η) := by
      refine mul_le_mul_of_nonneg_right ?_ hLη
      simp only [C₁]
      have : 0 ≤ fullConst d κ * tailInt + 8 * farConst d κ + 4 * nearConst d + sInt d := by
        positivity
      linarith
    have k3 : C₁ * L ^ (-1 + η) ≤ C₁ * (L ^ (-1 + η) + iξ + iζ) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₁
    linarith

/-- The master bound for the nonzero modes. -/
theorem lintegral_nonzeroModes_le (hd : 3 ≤ d) {κ η : ℝ} (hκ : 0 < κ)
    (hη : η ≤ 1 / 20) : ∀ (D L lam : ℝ) (Φ : ℝ → Mom d → Mom d → ℂ),
      1 ≤ L → 1 ≤ lam → lam ≤ L ^ η → (∀ s, NTBounds (10 * d) D (Φ s)) →
      (∀ s, κ * L < |s| → ∀ x y, Φ s x y = 0) → ∀ a b ξ ζ : Mom d,
      ∫⁻ s, ‖∑' gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0},
          ntIntegral lam (Φ s) a b (L • intVec gh.1.1 + ξ) (L • intVec gh.1.2 + ζ) s‖ₑ ≤
        ENNReal.ofReal (termConst d (10 * d) * modeConst d κ * D * lam ^ (2 * d) *
          (L ^ (-1 + η) + {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ξ +
            {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ζ)) := by
  intro D L lam Φ hL hlam hle hΦ hsupp a b ξ ζ
  set N := 10 * d
  have hD : 0 ≤ D := (hΦ 0).nonneg
  have hN1 : d + 1 ≤ N := by omega
  set K := termConst d N * D * lam ^ (2 * d)
  have hK : 0 ≤ K := by
    have := termConst_nonneg d N; have : 0 ≤ lam := by linarith
    positivity
  set M : ℝ → ℝ≥0∞ := fun s => {s : ℝ | |s| ≤ κ * L}.indicator
    (fun s => modeSum d N L lam s a b ξ ζ) s
  have hstep1 : ∀ s, ‖∑' gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0},
      ntIntegral lam (Φ s) a b (L • intVec gh.1.1 + ξ) (L • intVec gh.1.2 + ζ) s‖ₑ ≤
      ENNReal.ofReal K * M s := fun s => by
    by_cases hs : |s| ≤ κ * L
    · simp only [M, Set.indicator_of_mem (show s ∈ {s : ℝ | |s| ≤ κ * L} from hs)]
      exact enorm_tsum_nonzero_le hN1 (hΦ s) hlam a b ξ ζ
    · have h0 : ∀ gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0},
          ntIntegral lam (Φ s) a b (L • intVec gh.1.1 + ξ) (L • intVec gh.1.2 + ζ) s = 0 :=
        fun gh => ntIntegral_eq_zero (hsupp s (not_le.1 hs)) _ _ _ _ s
      simp only [h0, tsum_zero, enorm_zero]
      exact bot_le
  have hstep2 := lintegral_modeSum_le hd hκ hη hL hlam hle a b ξ ζ
  calc ∫⁻ s, ‖∑' gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0},
        ntIntegral lam (Φ s) a b (L • intVec gh.1.1 + ξ) (L • intVec gh.1.2 + ζ) s‖ₑ
      ≤ ∫⁻ s, ENNReal.ofReal K * M s := lintegral_mono hstep1
    _ = ENNReal.ofReal K * ∫⁻ s, M s := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine (mul_le_mul_right hstep2 _).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul hK]
        congr 1
        simp only [K]
        ring

/-! ### The statements of DH23 Lemma 6.5 (2) -/

theorem summable_norm_ntIntegral (hd : 1 ≤ d) {κ D L lam : ℝ} (hκ : 0 ≤ κ) (hL : 1 ≤ L)
    (hlam : 1 ≤ lam) {Φ : ℝ → Mom d → Mom d → ℂ} (hΦ : ∀ s, NTBounds (10 * d) D (Φ s))
    (hsupp : ∀ s, κ * L < |s| → ∀ x y, Φ s x y = 0) (a b ξ ζ : Mom d) (s : ℝ) :
    Summable fun gh : (Fin d → ℤ) × (Fin d → ℤ) =>
      ‖ntIntegral lam (Φ s) a b (L • intVec gh.1 + ξ) (L • intVec gh.2 + ζ) s‖ := by
  by_cases hs : |s| ≤ κ * L
  · obtain ⟨hsum, -⟩ := summable_tsum_termBound_le (N := 10 * d) (by omega) hL hκ hs hlam a b ξ ζ
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun gh => norm_ntIntegral_le (by omega) (hΦ s) hlam a b _ _ s)
      (hsum.mul_left (termConst d (10 * d) * D * lam ^ (2 * d)))
  · have h0 : ∀ gh : (Fin d → ℤ) × (Fin d → ℤ),
        ntIntegral lam (Φ s) a b (L • intVec gh.1 + ξ) (L • intVec gh.2 + ζ) s = 0 :=
      fun gh => ntIntegral_eq_zero (hsupp s (not_le.1 hs)) _ _ _ _ s
    simp only [h0, norm_zero]
    exact summable_zero

theorem indicator_half_le {L : ℝ} (hL : 1 ≤ L) {η : ℝ} (hη0 : 0 ≤ η) (x : Mom d) :
    {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => (1 : ℝ)) x ≤ 2 * ‖x‖ * L ^ (-1 + 2 * η) := by
  have hL0 : 0 < L := by linarith
  have hLi : L⁻¹ ≤ L ^ (-1 + 2 * η) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  by_cases hx : x ∈ {x : Mom d | L / 2 < ‖x‖}
  · rw [Set.indicator_of_mem hx]
    have hx' : L / 2 < ‖x‖ := hx
    calc (1 : ℝ) ≤ 2 * ‖x‖ * L⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hL0]; linarith
      _ ≤ 2 * ‖x‖ * L ^ (-1 + 2 * η) := by gcongr
  · rw [Set.indicator_of_notMem hx]; positivity

/-- **DH23 Lemma 6.5 (2)** (`NTSP`, (NTSPest), L1025–L1031). Let `d ≥ 3`, `κ > 0`,
`0 ≤ η ≤ 1/20`. For `L ≥ 1`, `1 ≤ λ ≤ L^η` (DH23 uses `λ ≤ (log L)^4`), and `Φ(s, ·, ·)`
satisfying (NTphibounds) through order `10d` with constant `D` and supported in `|s| ≤ κL`, the
Poisson sums converge absolutely for every `s`, and uniformly in `(a, b) ∈ ℝ^{2d}`:
`∫_ℝ |∑_{(g,h) ≠ 0} ∫∫ χ₀((x-a)/λ) χ₀((y-b)/λ) Φ(s,x,y) e[(Lg+ξ)·x + (Lh+ζ)·y + s⟨x,y⟩] dx dy| ds
  ≤ C D λ^{2d} L^{-1+2η} (1 + |ξ| + |ζ|)`.
(The proof gives `C D λ^{2d}(L^{-1+η} + 1_{|ξ| > L/2} + 1_{|ζ| > L/2})`,
`lintegral_nonzeroModes_le`.) -/
theorem ntsp_two (d : ℕ) (hd : 3 ≤ d) {κ η : ℝ} (hκ : 0 < κ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 20) :
    ∃ C : ℝ, ∀ (D L lam : ℝ) (Φ : ℝ → Mom d → Mom d → ℂ),
      1 ≤ L → 1 ≤ lam → lam ≤ L ^ η → (∀ s, NTBounds (10 * d) D (Φ s)) →
      (∀ s, κ * L < |s| → ∀ x y, Φ s x y = 0) → ∀ a b ξ ζ : Mom d,
      (∀ s, Summable fun gh : (Fin d → ℤ) × (Fin d → ℤ) =>
        ‖ntIntegral lam (Φ s) a b (L • intVec gh.1 + ξ) (L • intVec gh.2 + ζ) s‖) ∧
      ∫⁻ s, ‖∑' gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0},
          ntIntegral lam (Φ s) a b (L • intVec gh.1.1 + ξ) (L • intVec gh.1.2 + ζ) s‖ₑ ≤
        ENNReal.ofReal (C * D * lam ^ (2 * d) * L ^ (-1 + 2 * η) * (1 + ‖ξ‖ + ‖ζ‖)) := by
  refine ⟨2 * (termConst d (10 * d) * modeConst d κ),
    fun D L lam Φ hL hlam hle hΦ hsupp a b ξ ζ => ⟨fun s =>
      summable_norm_ntIntegral (by omega) hκ.le hL hlam hΦ hsupp a b ξ ζ s, ?_⟩⟩
  refine (lintegral_nonzeroModes_le hd hκ hη D L lam Φ hL hlam hle hΦ hsupp a b ξ ζ).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hD : 0 ≤ D := (hΦ 0).nonneg
  have hC : 0 ≤ termConst d (10 * d) * modeConst d κ * D * lam ^ (2 * d) := by
    have := termConst_nonneg d (10 * d); have := modeConst_nonneg d hκ.le
    have : 0 ≤ lam := by linarith
    positivity
  have h1 : L ^ (-1 + η) ≤ L ^ (-1 + 2 * η) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h2 := indicator_half_le hL hη0 ξ
  have h3 := indicator_half_le hL hη0 ζ
  have hLη : 0 ≤ L ^ (-1 + 2 * η) := by positivity
  calc termConst d (10 * d) * modeConst d κ * D * lam ^ (2 * d) *
        (L ^ (-1 + η) + {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ξ +
          {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ζ)
      ≤ termConst d (10 * d) * modeConst d κ * D * lam ^ (2 * d) *
          (2 * L ^ (-1 + 2 * η) * (1 + ‖ξ‖ + ‖ζ‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        nlinarith [norm_nonneg ξ, norm_nonneg ζ]
    _ = _ := by ring

/-- **DH23 Lemma 6.5, (NTSPest2)** (L1032–L1035): under the hypotheses of `ntsp_two`, the full
Poisson sum (including `(g, h) = 0`) is bounded uniformly in `(ξ, ζ, a, b)`:
`∫_ℝ |∑_{(g,h)} ∫∫ … ds| ≤ C D λ^{2d}`. -/
theorem ntsp_two_all (d : ℕ) (hd : 3 ≤ d) {κ η : ℝ} (hκ : 0 < κ) (hη : η ≤ 1 / 20) :
    ∃ C : ℝ, ∀ (D L lam : ℝ) (Φ : ℝ → Mom d → Mom d → ℂ),
      1 ≤ L → 1 ≤ lam → lam ≤ L ^ η → (∀ s, NTBounds (10 * d) D (Φ s)) →
      (∀ s, κ * L < |s| → ∀ x y, Φ s x y = 0) → ∀ a b ξ ζ : Mom d,
      ∫⁻ s, ‖∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
          ntIntegral lam (Φ s) a b (L • intVec gh.1 + ξ) (L • intVec gh.2 + ζ) s‖ₑ ≤
        ENNReal.ofReal (C * D * lam ^ (2 * d)) := by
  refine ⟨termConst d (10 * d) * (sInt d + 3 * modeConst d κ),
    fun D L lam Φ hL hlam hle hΦ hsupp a b ξ ζ => ?_⟩
  set N := 10 * d
  have hD : 0 ≤ D := (hΦ 0).nonneg
  set K := termConst d N * D * lam ^ (2 * d)
  have hK : 0 ≤ K := by
    have := termConst_nonneg d N; have : 0 ≤ lam := by linarith
    positivity
  set M : ℝ → ℝ≥0∞ := fun s => {s : ℝ | |s| ≤ κ * L}.indicator
    (fun s => modeSum d N L lam s a b ξ ζ) s
  set J : ℝ → (Fin d → ℤ) × (Fin d → ℤ) → ℂ := fun s gh =>
    ntIntegral lam (Φ s) a b (L • intVec gh.1 + ξ) (L • intVec gh.2 + ζ) s
  have hpt : ∀ s, ‖∑' gh, J s gh‖ₑ ≤ ENNReal.ofReal (K * ((1 + |s|) ^ d)⁻¹) +
      ENNReal.ofReal K * M s := fun s => by
    by_cases hs : |s| ≤ κ * L
    · have hsum : Summable (J s) :=
        (summable_norm_ntIntegral (by omega) hκ.le hL hlam hΦ hsupp a b ξ ζ s).of_norm
      rw [hsum.tsum_eq_add_tsum_ite 0]
      refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_ntIntegral_le_stat (by omega) (hΦ s) hlam a b _ _ s)
      · have he : ∑' gh, (if gh = 0 then 0 else J s gh) =
            ∑' gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0},
              ntIntegral lam (Φ s) a b (L • intVec gh.1.1 + ξ) (L • intVec gh.1.2 + ζ) s := by
          have h1 : (∑' gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0},
              ntIntegral lam (Φ s) a b (L • intVec gh.1.1 + ξ) (L • intVec gh.1.2 + ζ) s) =
              ∑' gh, ({gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0} : Set _).indicator (J s) gh :=
            tsum_subtype ({gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0}) (J s)
          rw [h1]
          refine tsum_congr fun gh => ?_
          by_cases h0 : gh = 0
          · simp [h0]
          · simp [h0, J]
        rw [he]
        simp only [M, Set.indicator_of_mem (show s ∈ {s : ℝ | |s| ≤ κ * L} from hs)]
        exact enorm_tsum_nonzero_le (by omega) (hΦ s) hlam a b ξ ζ
    · have h0 : ∀ gh, J s gh = 0 := fun gh => ntIntegral_eq_zero (hsupp s (not_le.1 hs)) _ _ _ _ s
      simp only [h0, tsum_zero, enorm_zero]
      exact bot_le
  have hstep2 := lintegral_modeSum_le hd hκ hη hL hlam hle a b ξ ζ
  have hc : Continuous fun s : ℝ => K * ((1 + |s|) ^ d)⁻¹ :=
    continuous_const.mul (Continuous.inv₀ (by fun_prop) (fun s => by positivity))
  have hm := modeConst_nonneg d hκ.le
  have hLη : L ^ (-1 + η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hi : ∀ x : Mom d, {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => (1 : ℝ)) x ≤ 1 :=
    fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x |>.trans le_rfl
  calc ∫⁻ s, ‖∑' gh, J s gh‖ₑ
      ≤ ∫⁻ s, (ENNReal.ofReal (K * ((1 + |s|) ^ d)⁻¹) + ENNReal.ofReal K * M s) :=
        lintegral_mono hpt
    _ = (∫⁻ s, ENNReal.ofReal (K * ((1 + |s|) ^ d)⁻¹)) + ENNReal.ofReal K * ∫⁻ s, M s := by
        rw [lintegral_add_left (f := fun s => ENNReal.ofReal (K * ((1 + |s|) ^ d)⁻¹))
            (ENNReal.measurable_ofReal.comp hc.measurable),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (K * sInt d) + ENNReal.ofReal K * ENNReal.ofReal (modeConst d κ *
          (L ^ (-1 + η) + {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ξ +
            {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => 1) ζ)) := by
        gcongr
        · exact lintegral_le_of_le_inv_pow (by omega) hK fun s => le_rfl
    _ ≤ ENNReal.ofReal (K * sInt d) + ENNReal.ofReal K * ENNReal.ofReal (modeConst d κ * 3) := by
        gcongr
        linarith [hi ξ, hi ζ]
    _ = ENNReal.ofReal (termConst d (10 * d) * (sInt d + 3 * modeConst d κ) * D * lam ^ (2 * d)) := by
        rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add (by have := sInt_nonneg d; positivity)
          (by positivity)]
        congr 1
        simp only [K, N]
        ring

end WaveTurbulence.NTSP
