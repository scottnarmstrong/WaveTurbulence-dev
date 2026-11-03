/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IJI

/-!
# DH21 Lemma 5.6: weight splits and the class `J` pieces

The weight `(1 + Σ|α_j| + |α₁| + |γ₁'|)^θ` of the composed operator is split using
`|α₁| ≤ |y| + |ℓ| + |γ₁|` (the denominator `ℓ + εα₁ + γ₁`) and `|γ₂| ≤ |x| + |γ₁| + |α₁|` (the
denominator `γ₁ + γ₂ + εα₁`), as in DH21 L1064. The generic `exists_piece_IJI` turns a coupling
with a `Γ` bound into a basic class `J` operator on `(ι ⊕ Empty) ⊕ Unit`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

variable {ι : Type*} [Fintype ι]

section Splits

variable {θ : ℝ} {ε : ℤ}

theorem sum_enorm_IJI (α : (ι ⊕ Empty) ⊕ Unit → ℝ) :
    ∑ j, ‖α j‖ₑ = ∑ i, ‖vA α i‖ₑ + ‖α (Sum.inr ())‖ₑ := by
  rw [sum_enorm_y3]; simp

theorem enorm_rpow_le_wJ (h0 : 0 ≤ θ) (b : ι → ℝ) (γ₁ : ℝ) : ‖γ₁‖ₑ ^ θ ≤ wJ θ b γ₁ :=
  rpow_mono' h0 le_add_self

/-- `|α₁|^θ ≤ |y|^θ + 2 wJ(α', γ₁)` with `y = ℓ + γ₁ + εα₁`. -/
theorem special_IJI_le (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {y : ι → ℤ}
    (hy : IsBundle y) (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ : ℝ) :
    ‖α (Sum.inr ())‖ₑ ^ θ ≤ ‖bundle y (vA α) + γ₁ + ε * α (Sum.inr ())‖ₑ ^ θ +
      2 * wJ θ (vA α) γ₁ := by
  have hs := special_rpow_le h0 h1 hε (α (Sum.inr ())) (bundle y (vA α)) γ₁
    (abs_bundle_le hy _)
  have ha := sum_rpow_le_wJ h0 (vA α) γ₁
  have hg := enorm_rpow_le_wJ h0 (vA α) γ₁
  calc _ ≤ _ := hs
    _ ≤ ‖bundle y (vA α) + γ₁ + ε * α (Sum.inr ())‖ₑ ^ θ + wJ θ (vA α) γ₁ +
          wJ θ (vA α) γ₁ := add_le_add (add_le_add le_rfl ha) hg
    _ = _ := by ring

theorem wJ_IJI_eq (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ : ℝ) :
    wJ θ α γ = (1 + (∑ i, ‖vA α i‖ₑ + ‖α (Sum.inr ())‖ₑ) + ‖γ‖ₑ) ^ θ := by
  rw [wJ, sum_enorm_IJI]

/-- Split of DH21 term I (`γ₁' = σ₁ + σ₂`). -/
theorem split_IJI_aa (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {y : ι → ℤ}
    (hy : IsBundle y) (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ σ₁ σ₂ : ℝ) :
    wJ θ α (σ₁ + σ₂) ≤ 3 * wJ θ (vA α) γ₁ +
      ((1 + ‖bundle y (vA α) + γ₁ + ε * α (Sum.inr ())‖ₑ) + (1 + ‖σ₁‖ₑ) + (1 + ‖σ₂‖ₑ)) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set e := ‖α (Sum.inr ())‖ₑ
  set Y := bundle y (vA α) + γ₁ + ε * α (Sum.inr ())
  have hW : (1 + a + ‖γ₁‖ₑ) ^ θ = wJ θ (vA α) γ₁ := rfl
  have hs := special_IJI_le h0 h1 hε hy α γ₁
  have hY := rpow_le_one_add h0 h1 ‖Y‖ₑ
  rw [wJ_IJI_eq]
  calc (1 + (a + e) + ‖σ₁ + σ₂‖ₑ) ^ θ ≤ ((1 + a + ‖γ₁‖ₑ) + e + ‖σ₁‖ₑ + ‖σ₂‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + e) + ‖σ₁ + σ₂‖ₑ ≤ 1 + (a + e) + (‖σ₁‖ₑ + ‖σ₂‖ₑ) := by
              gcongr; exact enorm_add_le _ _
          _ ≤ 1 + (a + e) + (‖σ₁‖ₑ + ‖σ₂‖ₑ) + ‖γ₁‖ₑ := le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + e ^ θ + ‖σ₁‖ₑ ^ θ + ‖σ₂‖ₑ ^ θ := rpow_add4_le h0 h1 _ _ _ _
    _ ≤ wJ θ (vA α) γ₁ + ((1 + ‖Y‖ₑ) + 2 * wJ θ (vA α) γ₁) + (1 + ‖σ₁‖ₑ) + (1 + ‖σ₂‖ₑ) := by
        rw [hW]
        exact add_le_add (add_le_add (add_le_add le_rfl (hs.trans (add_le_add hY le_rfl)))
          (rpow_le_one_add h0 h1 _)) (rpow_le_one_add h0 h1 _)
    _ = _ := by ring

/-- Split of DH21 term II (`γ₁' = γ₁ + γ₂` and `γ₁' = σ₁`). -/
theorem split_IJI_ab (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {y : ι → ℤ}
    (hy : IsBundle y) (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ γ₂ σ₁ : ℝ) :
    wJ θ α (γ₁ + γ₂) ≤ 5 * wJ θ (vA α) γ₁ +
      (2 * (1 + ‖bundle y (vA α) + γ₁ + ε * α (Sum.inr ())‖ₑ) +
        (1 + ‖γ₁ + γ₂ + ε * α (Sum.inr ()) - σ₁‖ₑ) ^ θ + (1 + ‖σ₁‖ₑ)) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set e := ‖α (Sum.inr ())‖ₑ
  set Y := bundle y (vA α) + γ₁ + ε * α (Sum.inr ())
  set U := γ₁ + γ₂ + ε * α (Sum.inr ()) - σ₁
  have hW : (1 + a + ‖γ₁‖ₑ) ^ θ = wJ θ (vA α) γ₁ := rfl
  have hs := special_IJI_le h0 h1 hε hy α γ₁
  have hY := rpow_le_one_add h0 h1 ‖Y‖ₑ
  have hε1 : ‖(ε : ℝ) * α (Sum.inr ())‖ₑ = e := by
    rw [enorm_mul]; rcases hε with rfl | rfl <;> simp [e]
  have hg : ‖γ₁ + γ₂‖ₑ ≤ ‖U‖ₑ + ‖σ₁‖ₑ + e := by
    rw [show γ₁ + γ₂ = U + σ₁ + -(ε * α (Sum.inr ())) by simp only [U]; ring]
    refine (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) ?_)
    rw [enorm_neg, hε1]
  have h2 : ∀ u : ℝ≥0∞, (u + u) ^ θ ≤ 2 * u ^ θ := fun u =>
    (rpow_add_le h0 h1 u u).trans_eq (two_mul _).symm
  have hU : ‖U‖ₑ ^ θ ≤ (1 + ‖U‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  rw [wJ_IJI_eq]
  calc (1 + (a + e) + ‖γ₁ + γ₂‖ₑ) ^ θ ≤ ((1 + a + ‖γ₁‖ₑ) + (e + e) + ‖U‖ₑ + ‖σ₁‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + e) + ‖γ₁ + γ₂‖ₑ ≤ 1 + (a + e) + (‖U‖ₑ + ‖σ₁‖ₑ + e) := by gcongr
          _ ≤ 1 + (a + e) + (‖U‖ₑ + ‖σ₁‖ₑ + e) + ‖γ₁‖ₑ := le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + (e + e) ^ θ + ‖U‖ₑ ^ θ + ‖σ₁‖ₑ ^ θ := rpow_add4_le h0 h1 _ _ _ _
    _ ≤ wJ θ (vA α) γ₁ + 2 * ((1 + ‖Y‖ₑ) + 2 * wJ θ (vA α) γ₁) + (1 + ‖U‖ₑ) ^ θ +
          (1 + ‖σ₁‖ₑ) := by
        rw [hW]
        exact add_le_add (add_le_add (add_le_add le_rfl ((h2 e).trans
          (mul_le_mul' le_rfl (hs.trans (add_le_add hY le_rfl))))) hU)
          (rpow_le_one_add h0 h1 _)
    _ = _ := by ring

theorem split_IJI_ac (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {y : ι → ℤ}
    (hy : IsBundle y) (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ γ₂ σ₁ : ℝ) :
    wJ θ α σ₁ ≤ 5 * wJ θ (vA α) γ₁ +
      (2 * (1 + ‖bundle y (vA α) + γ₁ + ε * α (Sum.inr ())‖ₑ) +
        (1 + ‖γ₁ + γ₂ + ε * α (Sum.inr ()) - σ₁‖ₑ) ^ θ + (1 + ‖σ₁‖ₑ)) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set e := ‖α (Sum.inr ())‖ₑ
  set Y := bundle y (vA α) + γ₁ + ε * α (Sum.inr ())
  set U := γ₁ + γ₂ + ε * α (Sum.inr ()) - σ₁
  have hW : (1 + a + ‖γ₁‖ₑ) ^ θ = wJ θ (vA α) γ₁ := rfl
  have hs := special_IJI_le h0 h1 hε hy α γ₁
  have hY := rpow_le_one_add h0 h1 ‖Y‖ₑ
  rw [wJ_IJI_eq]
  calc (1 + (a + e) + ‖σ₁‖ₑ) ^ θ ≤ ((1 + a + ‖γ₁‖ₑ) + e + ‖σ₁‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + e) + ‖σ₁‖ₑ ≤ 1 + (a + e) + ‖σ₁‖ₑ + ‖γ₁‖ₑ := le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + e ^ θ + ‖σ₁‖ₑ ^ θ := rpow_add3_le h0 h1 _ _ _
    _ ≤ wJ θ (vA α) γ₁ + ((1 + ‖Y‖ₑ) + 2 * wJ θ (vA α) γ₁) + (1 + ‖σ₁‖ₑ) := by
        rw [hW]
        exact add_le_add (add_le_add le_rfl (hs.trans (add_le_add hY le_rfl)))
          (rpow_le_one_add h0 h1 _)
    _ ≤ wJ θ (vA α) γ₁ + ((1 + ‖Y‖ₑ) + 2 * wJ θ (vA α) γ₁) + (1 + ‖σ₁‖ₑ) +
          (2 * wJ θ (vA α) γ₁ + (1 + ‖Y‖ₑ) + (1 + ‖U‖ₑ) ^ θ) := le_self_add
    _ = _ := by ring

/-- Split of DH21 term III (`γ₁' = σ`). -/
theorem split_IJI_ca (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {y : ι → ℤ}
    (hy : IsBundle y) (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ σ : ℝ) :
    wJ θ α σ ≤ 3 * wJ θ (vA α) γ₁ +
      ((1 + ‖bundle y (vA α) + γ₁ + ε * α (Sum.inr ())‖ₑ) + (1 + ‖σ‖ₑ)) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set e := ‖α (Sum.inr ())‖ₑ
  set Y := bundle y (vA α) + γ₁ + ε * α (Sum.inr ())
  have hW : (1 + a + ‖γ₁‖ₑ) ^ θ = wJ θ (vA α) γ₁ := rfl
  have hs := special_IJI_le h0 h1 hε hy α γ₁
  have hY := rpow_le_one_add h0 h1 ‖Y‖ₑ
  rw [wJ_IJI_eq]
  calc (1 + (a + e) + ‖σ‖ₑ) ^ θ ≤ ((1 + a + ‖γ₁‖ₑ) + e + ‖σ‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + e) + ‖σ‖ₑ ≤ 1 + (a + e) + ‖σ‖ₑ + ‖γ₁‖ₑ := le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + e ^ θ + ‖σ‖ₑ ^ θ := rpow_add3_le h0 h1 _ _ _
    _ ≤ wJ θ (vA α) γ₁ + ((1 + ‖Y‖ₑ) + 2 * wJ θ (vA α) γ₁) + (1 + ‖σ‖ₑ) := by
        rw [hW]
        exact add_le_add (add_le_add le_rfl (hs.trans (add_le_add hY le_rfl)))
          (rpow_le_one_add h0 h1 _)
    _ = _ := by ring

/-- Split of DH21 term IV (`γ₁' = γ₁ + γ₂`). -/
theorem split_IJI_cb (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {y : ι → ℤ}
    (hy : IsBundle y) (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ γ₂ : ℝ) :
    wJ θ α (γ₁ + γ₂) ≤ 5 * wJ θ (vA α) γ₁ +
      2 * ((1 + ‖bundle y (vA α) + γ₁ + ε * α (Sum.inr ())‖ₑ) ^ θ +
        2 * (1 + ‖γ₁ + γ₂ + ε * α (Sum.inr ())‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set e := ‖α (Sum.inr ())‖ₑ
  set Y := bundle y (vA α) + γ₁ + ε * α (Sum.inr ())
  set X := γ₁ + γ₂ + ε * α (Sum.inr ())
  have hW : (1 + a + ‖γ₁‖ₑ) ^ θ = wJ θ (vA α) γ₁ := rfl
  have hs := special_IJI_le h0 h1 hε hy α γ₁
  have hY : ‖Y‖ₑ ^ θ ≤ (1 + ‖Y‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hX : ‖X‖ₑ ^ θ ≤ (1 + ‖X‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hε1 : ‖(ε : ℝ) * α (Sum.inr ())‖ₑ = e := by
    rw [enorm_mul]; rcases hε with rfl | rfl <;> simp [e]
  have hg : ‖γ₁ + γ₂‖ₑ ≤ ‖X‖ₑ + e := by
    rw [show γ₁ + γ₂ = X + -(ε * α (Sum.inr ())) by simp only [X]; ring]
    refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [enorm_neg, hε1]
  have h2 : ∀ u : ℝ≥0∞, (u + u) ^ θ ≤ 2 * u ^ θ := fun u =>
    (rpow_add_le h0 h1 u u).trans_eq (two_mul _).symm
  rw [wJ_IJI_eq]
  calc (1 + (a + e) + ‖γ₁ + γ₂‖ₑ) ^ θ ≤ ((1 + a + ‖γ₁‖ₑ) + (e + e) + ‖X‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + e) + ‖γ₁ + γ₂‖ₑ ≤ 1 + (a + e) + (‖X‖ₑ + e) := by gcongr
          _ ≤ 1 + (a + e) + (‖X‖ₑ + e) + ‖γ₁‖ₑ := le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + (e + e) ^ θ + ‖X‖ₑ ^ θ := rpow_add3_le h0 h1 _ _ _
    _ ≤ wJ θ (vA α) γ₁ + 2 * ((1 + ‖Y‖ₑ) ^ θ + 2 * wJ θ (vA α) γ₁) + (1 + ‖X‖ₑ) ^ θ := by
        rw [hW]
        exact add_le_add (add_le_add le_rfl ((h2 e).trans
          (mul_le_mul' le_rfl (hs.trans (add_le_add hY le_rfl))))) hX
    _ ≤ wJ θ (vA α) γ₁ + 2 * ((1 + ‖Y‖ₑ) ^ θ + 2 * wJ θ (vA α) γ₁) + (1 + ‖X‖ₑ) ^ θ +
          (3 * (1 + ‖X‖ₑ) ^ θ + 2) := le_self_add
    _ = _ := by ring

theorem split_IJI_cc (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {y : ι → ℤ}
    (hy : IsBundle y) (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ γ₂ : ℝ) :
    wJ θ α 0 ≤ 5 * wJ θ (vA α) γ₁ +
      2 * ((1 + ‖bundle y (vA α) + γ₁ + ε * α (Sum.inr ())‖ₑ) ^ θ +
        2 * (1 + ‖γ₁ + γ₂ + ε * α (Sum.inr ())‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set e := ‖α (Sum.inr ())‖ₑ
  set Y := bundle y (vA α) + γ₁ + ε * α (Sum.inr ())
  set X := γ₁ + γ₂ + ε * α (Sum.inr ())
  have hW : (1 + a + ‖γ₁‖ₑ) ^ θ = wJ θ (vA α) γ₁ := rfl
  have hs := special_IJI_le h0 h1 hε hy α γ₁
  have hY : ‖Y‖ₑ ^ θ ≤ (1 + ‖Y‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  rw [wJ_IJI_eq]
  calc (1 + (a + e) + ‖(0 : ℝ)‖ₑ) ^ θ ≤ ((1 + a + ‖γ₁‖ₑ) + e) ^ θ := by
        refine rpow_mono' h0 ?_
        rw [enorm_zero, add_zero]
        calc 1 + (a + e) ≤ 1 + (a + e) + ‖γ₁‖ₑ := le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + e ^ θ := rpow_add_le h0 h1 _ _
    _ ≤ wJ θ (vA α) γ₁ + ((1 + ‖Y‖ₑ) ^ θ + 2 * wJ θ (vA α) γ₁) := by
        rw [hW]; exact add_le_add le_rfl (hs.trans (add_le_add hY le_rfl))
    _ ≤ wJ θ (vA α) γ₁ + ((1 + ‖Y‖ₑ) ^ θ + 2 * wJ θ (vA α) γ₁) +
          (2 * wJ θ (vA α) γ₁ + (1 + ‖Y‖ₑ) ^ θ + 4 * (1 + ‖X‖ₑ) ^ θ + 2) := le_self_add
    _ = _ := by ring

end Splits

end WaveTurbulence.ClassJR
