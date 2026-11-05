/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3ZModel

/-!
# X3: the parametrix gives `(1 − ℒ₁)^{-1}` on `Z` (T L2333–L2336)

`parametrix_invert` takes an operator `A = 1 − ℒ₁` on `Z` with a left and a right parametrix:
`A 𝒳 = 1 − 𝒴` and `𝒳 A = 1 − 𝒲`, where `‖𝒴‖, ‖𝒲‖ ≤ ½`, `‖𝒳‖ ≤ M`, and `A`, `𝒴` are additive on `Z`. Then `A` is a
bijection of `Z` with `‖b‖_Z ≤ 2M ‖A b‖_Z`.
- The bound comes from `b = 𝒳(Ab) + 𝒲b`.
- Existence comes from solving `y = c + 𝒴y` by contraction (`exists_Z_fixedPoint`) and putting `b = 𝒳y`.
- Uniqueness comes from the bound.

This is TARGET's "`(1−ℒ₁)𝒳` and `𝒳(1−ℒ₁)` are both invertible, hence `1 − ℒ₁` is invertible and
`‖(1−ℒ₁)^{-1}‖ ≤ 2‖𝒳‖`".
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open Set
open scoped ENNReal NNReal

variable {d p : ℕ} {L Λ : ℝ}

theorem ZNorm_neg (f : ZTime p → (Fin d → ℤ) → ℂ) : ZNorm (d := d) L Λ (-f) = ZNorm L Λ f := by
  unfold ZNorm
  simp only [Pi.neg_apply, norm_neg]

theorem ZNorm_zero : ZNorm (d := d) (p := p) L Λ 0 = 0 := by
  unfold ZNorm
  simp

theorem zSpace_neg {f : ZTime p → (Fin d → ℤ) → ℂ} (hf : f ∈ ZSpace L Λ p) : -f ∈ ZSpace L Λ p :=
  ⟨fun n => (hf.1 n).neg, by rw [ZNorm_neg]; exact hf.2⟩

theorem zSpace_sub {f g : ZTime p → (Fin d → ℤ) → ℂ} (hf : f ∈ ZSpace L Λ p) (hg : g ∈ ZSpace L Λ p) :
    f - g ∈ ZSpace L Λ p := by
  rw [sub_eq_add_neg]
  exact zSpace_add hf (zSpace_neg hg)

theorem eq_zero_of_ZNorm_eq_zero {f : ZTime p → (Fin d → ℤ) → ℂ} (h : ZNorm (d := d) L Λ f = 0) : f = 0 := by
  funext t n
  have h1 : ENNReal.ofReal (zWeight L Λ n * ‖f t n‖) ≤ 0 := by
    rw [← h]
    exact le_iSup_of_le t (le_iSup (fun n => ENNReal.ofReal (zWeight L Λ n * ‖f t n‖)) n)
  have h2 : zWeight L Λ n * ‖f t n‖ ≤ 0 := ENNReal.ofReal_eq_zero.1 (le_antisymm h1 bot_le)
  have hw := zWeight_pos L Λ n
  have : ‖f t n‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h2) hw
  simpa using norm_le_zero_iff.1 this

/-- `a ≤ x + a/2` with `a < ⊤` gives `a ≤ 2x`. -/
theorem ennreal_le_two_mul_of_le_add_half {a x : ℝ≥0∞} (ha : a < ⊤) (h : a ≤ x + 2⁻¹ * a) : a ≤ 2 * x := by
  have hh : 2⁻¹ * a ≠ ⊤ := ENNReal.mul_ne_top (by simp) ha.ne
  have h2 : 2⁻¹ * a + 2⁻¹ * a = a := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  have h3 : 2⁻¹ * a ≤ x := by
    have : 2⁻¹ * a + 2⁻¹ * a ≤ x + 2⁻¹ * a := by rw [h2]; exact h
    exact (ENNReal.add_le_add_iff_right hh).1 this
  calc a = 2 * (2⁻¹ * a) := by rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
    _ ≤ 2 * x := by gcongr

theorem ennreal_inv_two_mul_ofReal (x : ℝ) : (2⁻¹ : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (x / 2) := by
  rw [div_eq_inv_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- **The parametrix gives the inverse.** -/
theorem parametrix_invert (A X Y W : (ZTime p → (Fin d → ℤ) → ℂ) → (ZTime p → (Fin d → ℤ) → ℂ))
    (M : ℝ≥0∞)
    (hAZ : ∀ b ∈ ZSpace L Λ p, A b ∈ ZSpace L Λ p) (hXZ : ∀ b ∈ ZSpace L Λ p, X b ∈ ZSpace L Λ p)
    (hYZ : ∀ b ∈ ZSpace L Λ p, Y b ∈ ZSpace L Λ p)
    (hAX : ∀ b ∈ ZSpace L Λ p, A (X b) = b - Y b) (hXA : ∀ b ∈ ZSpace L Λ p, X (A b) = b - W b)
    (hAlin : ∀ b ∈ ZSpace L Λ p, ∀ b' ∈ ZSpace L Λ p, A b - A b' = A (b - b'))
    (hYlin : ∀ b ∈ ZSpace L Λ p, ∀ b' ∈ ZSpace L Λ p, Y b - Y b' = Y (b - b'))
    (hX : ∀ b ∈ ZSpace L Λ p, ZNorm L Λ (X b) ≤ M * ZNorm L Λ b)
    (hY : ∀ b ∈ ZSpace L Λ p, ZNorm L Λ (Y b) ≤ 2⁻¹ * ZNorm L Λ b)
    (hW : ∀ b ∈ ZSpace L Λ p, ZNorm L Λ (W b) ≤ 2⁻¹ * ZNorm L Λ b) :
    (∀ b ∈ ZSpace L Λ p, ZNorm L Λ b ≤ 2 * M * ZNorm L Λ (A b)) ∧
    (∀ c ∈ ZSpace L Λ p, ∃! b, b ∈ ZSpace L Λ p ∧ A b = c) := by
  have hbound : ∀ b ∈ ZSpace L Λ p, ZNorm L Λ b ≤ 2 * M * ZNorm L Λ (A b) := by
    intro b hb
    have hsplit : b = X (A b) + W b := by rw [hXA b hb]; abel
    have h1 : ZNorm L Λ b ≤ M * ZNorm L Λ (A b) + 2⁻¹ * ZNorm L Λ b := by
      calc ZNorm L Λ b = ZNorm L Λ (X (A b) + W b) := by rw [← hsplit]
        _ ≤ ZNorm L Λ (X (A b)) + ZNorm L Λ (W b) := ZNorm_add_le L Λ _ _
        _ ≤ M * ZNorm L Λ (A b) + 2⁻¹ * ZNorm L Λ b := add_le_add (hX _ (hAZ b hb)) (hW b hb)
    rw [mul_assoc]
    exact ennreal_le_two_mul_of_le_add_half hb.2 h1
  refine ⟨hbound, fun c hc => ?_⟩
  -- existence: `y = c + 𝒴 y` by contraction, then `b = 𝒳 y`
  set r := 2 * (ZNorm L Λ c).toReal with hr
  have hr0 : 0 ≤ r := by positivity
  have hcr : ZNorm L Λ c = ENNReal.ofReal (r / 2) := by
    rw [hr, mul_div_cancel_left₀ _ two_ne_zero, ENNReal.ofReal_toReal hc.2.ne]
  obtain ⟨y, hyZ, -, hyR⟩ := exists_Z_fixedPoint (d := d) (p := p) L Λ r hr0
    (fun b y => y = c + Y b)
    (fun b hb hbr => ⟨c + Y b, zSpace_add hc (hYZ b hb), rfl, by
      calc ZNorm L Λ (c + Y b) ≤ ZNorm L Λ c + ZNorm L Λ (Y b) := ZNorm_add_le L Λ _ _
        _ ≤ ENNReal.ofReal (r / 2) + 2⁻¹ * ENNReal.ofReal r :=
            add_le_add hcr.le ((hY b hb).trans (by gcongr))
        _ = ENNReal.ofReal r := by
            rw [ennreal_inv_two_mul_ofReal r, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring⟩)
    (fun b hb b' hb' y hy y' hy' _ _ hR hR' => by
      rw [hR, hR', add_sub_add_left_eq_sub, hYlin b hb b' hb']
      refine (hY _ (zSpace_sub hb hb')).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div])
  refine ⟨X y, ⟨hXZ y hyZ, ?_⟩, fun b ⟨hbZ, hAb⟩ => ?_⟩
  · rw [hAX y hyZ]
    nth_rewrite 1 [hyR]
    abel
  · have hXyZ := hXZ y hyZ
    have hAy : A (X y) = c := by rw [hAX y hyZ]; nth_rewrite 1 [hyR]; abel
    have hdiff : A (b - X y) = 0 := by rw [← hAlin b hbZ (X y) hXyZ, hAb, hAy, sub_self]
    have := hbound (b - X y) (zSpace_sub hbZ hXyZ)
    rw [hdiff, ZNorm_zero, mul_zero] at this
    have h0 := eq_zero_of_ZNorm_eq_zero (le_antisymm this bot_le)
    exact sub_eq_zero.1 h0

end WaveTurbulence.Fixedpt
