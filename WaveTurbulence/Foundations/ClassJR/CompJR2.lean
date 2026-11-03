/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CompJR

/-!
# DH21 Lemma 5.4, `J R`: the forms, the weight splits and the weighted bounds of the pieces

The weight `(1 + Σ|α_j| + |γ₁'|)^θ` of the composed operator involves the special variable `α₁`;
as in DH21 L1013 it is replaced by `|x₁|^θ + |ℓ₂|^θ + |γ₅|^θ` with `x₁ = ℓ₂ + εα₁ + γ₅` the
argument of the factor `χ_∞(x₁)/x₁`, and the part `|γ₂ + γ₃|^θ` of `|γ₁'|^θ` (in the first `χ_∞`
piece) by `|x₀|^θ + |ℓ₃ - ℓ₁ + εα₁|^θ` (L1016).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

section Data

/-- The two forms `x₀ = ℓ₃ - ℓ₁ + εα₁ (+ γ₂ + γ₃)` and `x₁ = ℓ₂ + εα₁ (+ γ₅)`. -/
@[expose] def LsJR (R₁ : JSym ι₁) (R₂ : RSym ι₂) : Fin 2 → (ι₁ ⊕ ι₂) ⊕ Unit → ℤ :=
  ![y3 (fun i => -R₁.y i) R₂.y₂ R₂.ε, y3 0 R₂.y₁ R₂.ε]

/-- The constant parts `γ₂ + γ₃` and `γ₅` of the two forms. -/
@[expose] def csJR (Q : Type*) : Fin 2 → (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Q) → ℝ :=
  ![fun z => z.1.2 + z.2.1.1, fun z => z.2.1.2.2]

variable {R₁ : JSym ι₁} {R₂ : RSym ι₂}

theorem isBundle_LsJR {θ A N₁ N₂ : ℝ} (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    ∀ r, IsBundle (LsJR R₁ R₂ r) := by
  intro r; fin_cases r
  · exact isBundle_y3 (isBundle_neg h₁.bundle) h₂.bundle₂ (abs_sign_le h₂.sign)
  · exact isBundle_y3 isBundle_zero h₂.bundle₁ (abs_sign_le h₂.sign)

theorem measurable_csJR (Q : Type*) [MeasurableSpace Q] : ∀ r, Measurable (csJR Q r) := by
  intro r; fin_cases r
  · simp only [csJR]; exact (measurable_snd.comp measurable_fst).add
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
  · simp only [csJR]
    exact measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))

theorem formsV_JR_zero {Q : Type*} (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ)
    (z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Q)) :
    formsV (LsJR R₁ R₂) (csJR Q) α z 0 =
      bundle R₂.y₂ (vB α) - bundle R₁.y (vA α) + (z.1.2 + z.2.1.1) +
        R₂.ε * α (Sum.inr ()) := by
  simp only [formsV, LsJR, csJR, Matrix.cons_val, bundle_y3]
  have : bundle (fun i => -R₁.y i) (vA α) = -bundle R₁.y (vA α) := by
    simp [bundle, Finset.sum_neg_distrib]
  rw [this]
  ring

theorem formsV_JR_one {Q : Type*} (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ)
    (z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Q)) :
    formsV (LsJR R₁ R₂) (csJR Q) α z 1 =
      bundle R₂.y₁ (vB α) + z.2.1.2.2 + R₂.ε * α (Sum.inr ()) := by
  simp only [formsV, LsJR, csJR, Matrix.cons_val, bundle_y3]
  simp [bundle]
  ring

theorem vS_elim (a : ι₁ ⊕ ι₂ → ℝ) (s : Unit → ℝ) : (Sum.elim a s : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ)
    (Sum.inr ()) = s () := rfl

theorem vA_elim (a : ι₁ ⊕ ι₂ → ℝ) (s : Unit → ℝ) :
    vA (Sum.elim a s : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) = fun i => a (Sum.inl i) := rfl

theorem vB_elim (a : ι₁ ⊕ ι₂ → ℝ) (s : Unit → ℝ) :
    vB (Sum.elim a s : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) = fun i => a (Sum.inr i) := rfl

end Data

section Weights

theorem rpow_add4_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (a b c d : ℝ≥0∞) :
    (a + b + c + d) ^ θ ≤ a ^ θ + b ^ θ + c ^ θ + d ^ θ :=
  (rpow_add_le h0 h1 _ _).trans (add_le_add (rpow_add3_le h0 h1 _ _ _) le_rfl)

theorem sum_enorm_y3 (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) :
    ∑ j, ‖α j‖ₑ = ∑ i, ‖vA α i‖ₑ + ∑ i, ‖vB α i‖ₑ + ‖α (Sum.inr ())‖ₑ := by
  simp [Fintype.sum_sum_type, vA, vB]

theorem sum_rpow_le_wR {ι : Type*} [Fintype ι] {θ : ℝ} (h0 : 0 ≤ θ) (b : ι → ℝ)
    (γ₁ γ₃ : ℝ) : (∑ j, ‖b j‖ₑ) ^ θ ≤ wR θ b γ₁ γ₃ :=
  rpow_mono' h0 (le_add_right (le_add_right (le_add_left le_rfl)))

theorem enorm_rpow_le_wR {ι : Type*} [Fintype ι] {θ : ℝ} (h0 : 0 ≤ θ) (b : ι → ℝ)
    (γ₁ γ₃ : ℝ) : ‖γ₃‖ₑ ^ θ ≤ wR θ b γ₁ γ₃ :=
  rpow_mono' h0 (le_add_left le_rfl)

/-- `|α₁|^θ ≤ |x₁|^θ + |ℓ₂|^θ + |γ₅|^θ` with `x₁ = ℓ₂ + εα₁ + γ₅`. -/
theorem special_rpow_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (α₁ L γ₅ : ℝ) {S : ℝ≥0∞} (hL : ‖L‖ₑ ≤ S) :
    ‖α₁‖ₑ ^ θ ≤ ‖L + γ₅ + ε * α₁‖ₑ ^ θ + S ^ θ + ‖γ₅‖ₑ ^ θ := by
  have hα : ‖α₁‖ₑ ≤ ‖L + γ₅ + ε * α₁‖ₑ + S + ‖γ₅‖ₑ := by
    have e : α₁ = ε * (L + γ₅ + ε * α₁) - ε * L - ε * γ₅ := by
      rcases hε with rfl | rfl <;> push_cast <;> ring
    have hε1 : ‖(ε : ℝ)‖ₑ = 1 := by rcases hε with rfl | rfl <;> simp
    calc ‖α₁‖ₑ = ‖ε * (L + γ₅ + ε * α₁) - ε * L - ε * γ₅‖ₑ := by rw [← e]
      _ ≤ ‖ε * (L + γ₅ + ε * α₁)‖ₑ + ‖(ε : ℝ) * L‖ₑ + ‖(ε : ℝ) * γ₅‖ₑ :=
          enorm_sub_le.trans (add_le_add enorm_sub_le le_rfl)
      _ = ‖L + γ₅ + ε * α₁‖ₑ + ‖L‖ₑ + ‖γ₅‖ₑ := by simp only [enorm_mul, hε1, one_mul]
      _ ≤ _ := by gcongr
  exact (rpow_mono' h0 hα).trans (rpow_add3_le h0 h1 _ _ _)

end Weights

section Splits

variable {θ : ℝ} {ε : ℤ}

/-- The weight split of the `χ₀` piece of `J R`. -/
theorem wJ_split_JR_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {d : ι₂ → ℤ}
    (hd : IsBundle d) (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) (γ₁ γ₃ γ₅ σ : ℝ) :
    wJ θ α (γ₁ + σ) ≤ wJ θ (vA α) γ₁ + 3 * wR θ (vB α) γ₃ γ₅ +
      ((1 + ‖bundle d (vB α) + γ₅ + ε * α (Sum.inr ())‖ₑ) + (1 + ‖σ‖ₑ)) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set b := ∑ i, ‖vB α i‖ₑ
  set x1 := bundle d (vB α) + γ₅ + ε * α (Sum.inr ())
  have hs := special_rpow_le h0 h1 hε (α (Sum.inr ())) (bundle d (vB α)) γ₅ (abs_bundle_le hd _)
  have hbw : b ^ θ ≤ wR θ (vB α) γ₃ γ₅ := sum_rpow_le_wR h0 _ _ _
  have hgw : ‖γ₅‖ₑ ^ θ ≤ wR θ (vB α) γ₃ γ₅ := enorm_rpow_le_wR h0 _ _ _
  unfold wJ
  rw [sum_enorm_y3]
  calc (1 + (a + b + ‖α (Sum.inr ())‖ₑ) + ‖γ₁ + σ‖ₑ) ^ θ
      ≤ ((1 + a + ‖γ₁‖ₑ) + b + ‖α (Sum.inr ())‖ₑ + ‖σ‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + b + ‖α (Sum.inr ())‖ₑ) + ‖γ₁ + σ‖ₑ
            ≤ 1 + (a + b + ‖α (Sum.inr ())‖ₑ) + (‖γ₁‖ₑ + ‖σ‖ₑ) := by
              gcongr; exact enorm_add_le _ _
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + b ^ θ + ‖α (Sum.inr ())‖ₑ ^ θ + ‖σ‖ₑ ^ θ :=
        rpow_add4_le h0 h1 _ _ _ _
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ +
          (‖x1‖ₑ ^ θ + wR θ (vB α) γ₃ γ₅ + wR θ (vB α) γ₃ γ₅) + (1 + ‖σ‖ₑ) :=
        add_le_add (add_le_add (add_le_add le_rfl hbw)
          (hs.trans (add_le_add (add_le_add le_rfl hbw) hgw))) (rpow_le_one_add h0 h1 _)
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + 3 * wR θ (vB α) γ₃ γ₅ + ((1 + ‖x1‖ₑ) + (1 + ‖σ‖ₑ)) := by
        have := rpow_le_one_add h0 h1 ‖x1‖ₑ
        calc (1 + a + ‖γ₁‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ +
              (‖x1‖ₑ ^ θ + wR θ (vB α) γ₃ γ₅ + wR θ (vB α) γ₃ γ₅) + (1 + ‖σ‖ₑ)
            ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ +
              ((1 + ‖x1‖ₑ) + wR θ (vB α) γ₃ γ₅ + wR θ (vB α) γ₃ γ₅) + (1 + ‖σ‖ₑ) := by gcongr
          _ = _ := by ring

/-- The weight split of the first `χ_∞` piece of `J R` (`γ₁' = γ₁ + γ₂ + γ₃`). -/
theorem wJ_split_JR_P1 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {y : ι₁ → ℤ}
    {d ph : ι₂ → ℤ} (hy : IsBundle y) (hd : IsBundle d) (hph : IsBundle ph)
    (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) (γ₁ γ₂ γ₃ γ₅ : ℝ) :
    wJ θ α (γ₁ + (γ₂ + γ₃)) ≤ 2 * wJ θ (vA α) γ₁ + 6 * wR θ (vB α) γ₃ γ₅ +
      ((1 + ‖bundle ph (vB α) - bundle y (vA α) + (γ₂ + γ₃) + ε * α (Sum.inr ())‖ₑ) ^ θ +
        2 * (1 + ‖bundle d (vB α) + γ₅ + ε * α (Sum.inr ())‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set b := ∑ i, ‖vB α i‖ₑ
  set e := ‖α (Sum.inr ())‖ₑ
  set x0 := bundle ph (vB α) - bundle y (vA α) + (γ₂ + γ₃) + ε * α (Sum.inr ())
  set x1 := bundle d (vB α) + γ₅ + ε * α (Sum.inr ())
  have hε1 : ‖(ε : ℝ)‖ₑ = 1 := by rcases hε with rfl | rfl <;> simp
  have hx : ‖γ₂ + γ₃‖ₑ ≤ ‖x0‖ₑ + b + a + e := by
    have : γ₂ + γ₃ = x0 + -bundle ph (vB α) + bundle y (vA α) + -(ε * α (Sum.inr ())) := by
      simp only [x0]; ring
    rw [this]
    refine (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans
      (add_le_add ((enorm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)) ?_)
    · rw [enorm_neg]; exact abs_bundle_le hph _
    · exact abs_bundle_le hy _
    · rw [enorm_neg, enorm_mul, hε1, one_mul]
  have hs := special_rpow_le h0 h1 hε (α (Sum.inr ())) (bundle d (vB α)) γ₅ (abs_bundle_le hd _)
  have hbw : b ^ θ ≤ wR θ (vB α) γ₃ γ₅ := sum_rpow_le_wR h0 _ _ _
  have hgw : ‖γ₅‖ₑ ^ θ ≤ wR θ (vB α) γ₃ γ₅ := enorm_rpow_le_wR h0 _ _ _
  have haw : a ^ θ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ := rpow_mono' h0 (le_add_right (le_add_left le_rfl))
  have h2 : ∀ u : ℝ≥0∞, (u + u) ^ θ ≤ 2 * u ^ θ := fun u =>
    (rpow_add_le h0 h1 u u).trans_eq (two_mul _).symm
  have hx0 : ‖x0‖ₑ ^ θ ≤ (1 + ‖x0‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hx1 : ‖x1‖ₑ ^ θ ≤ (1 + ‖x1‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  unfold wJ
  rw [sum_enorm_y3]
  calc (1 + (a + b + e) + ‖γ₁ + (γ₂ + γ₃)‖ₑ) ^ θ
      ≤ (((1 + a + ‖γ₁‖ₑ) + a) + (b + b) + (e + e) + ‖x0‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + b + e) + ‖γ₁ + (γ₂ + γ₃)‖ₑ ≤ 1 + (a + b + e) + (‖γ₁‖ₑ + ‖γ₂ + γ₃‖ₑ) := by
              gcongr; exact enorm_add_le _ _
          _ ≤ 1 + (a + b + e) + (‖γ₁‖ₑ + (‖x0‖ₑ + b + a + e)) := by gcongr
          _ = _ := by ring
    _ ≤ ((1 + a + ‖γ₁‖ₑ) + a) ^ θ + (b + b) ^ θ + (e + e) ^ θ + ‖x0‖ₑ ^ θ :=
        rpow_add4_le h0 h1 _ _ _ _
    _ ≤ ((1 + a + ‖γ₁‖ₑ) ^ θ + a ^ θ) + 2 * b ^ θ + 2 * e ^ θ + ‖x0‖ₑ ^ θ :=
        add_le_add (add_le_add (add_le_add (rpow_add_le h0 h1 _ _) (h2 b)) (h2 e)) le_rfl
    _ ≤ ((1 + a + ‖γ₁‖ₑ) ^ θ + (1 + a + ‖γ₁‖ₑ) ^ θ) + 2 * wR θ (vB α) γ₃ γ₅ +
          2 * (‖x1‖ₑ ^ θ + wR θ (vB α) γ₃ γ₅ + wR θ (vB α) γ₃ γ₅) + (1 + ‖x0‖ₑ) ^ θ := by
        gcongr
        exact hs.trans (add_le_add (add_le_add le_rfl hbw) hgw)
    _ ≤ _ := by
        calc ((1 + a + ‖γ₁‖ₑ) ^ θ + (1 + a + ‖γ₁‖ₑ) ^ θ) + 2 * wR θ (vB α) γ₃ γ₅ +
              2 * (‖x1‖ₑ ^ θ + wR θ (vB α) γ₃ γ₅ + wR θ (vB α) γ₃ γ₅) + (1 + ‖x0‖ₑ) ^ θ
            ≤ ((1 + a + ‖γ₁‖ₑ) ^ θ + (1 + a + ‖γ₁‖ₑ) ^ θ) + 2 * wR θ (vB α) γ₃ γ₅ +
              2 * ((1 + ‖x1‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ + wR θ (vB α) γ₃ γ₅) +
                ((1 + ‖x0‖ₑ) ^ θ + 1) := by gcongr; exact le_self_add
          _ = _ := by ring

/-- The weight split of the second `χ_∞` piece of `J R` (`γ₁' = γ₁`). -/
theorem wJ_split_JR_P2 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {d : ι₂ → ℤ}
    (hd : IsBundle d) (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) (γ₁ γ₃ γ₅ : ℝ) (x0 : ℝ) :
    wJ θ α γ₁ ≤ wJ θ (vA α) γ₁ + 3 * wR θ (vB α) γ₃ γ₅ +
      ((1 + ‖x0‖ₑ) ^ θ + 2 * (1 + ‖bundle d (vB α) + γ₅ + ε * α (Sum.inr ())‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set b := ∑ i, ‖vB α i‖ₑ
  set x1 := bundle d (vB α) + γ₅ + ε * α (Sum.inr ())
  have hs := special_rpow_le h0 h1 hε (α (Sum.inr ())) (bundle d (vB α)) γ₅ (abs_bundle_le hd _)
  have hbw : b ^ θ ≤ wR θ (vB α) γ₃ γ₅ := sum_rpow_le_wR h0 _ _ _
  have hgw : ‖γ₅‖ₑ ^ θ ≤ wR θ (vB α) γ₃ γ₅ := enorm_rpow_le_wR h0 _ _ _
  have hx1 : ‖x1‖ₑ ^ θ ≤ (1 + ‖x1‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  unfold wJ
  rw [sum_enorm_y3]
  calc (1 + (a + b + ‖α (Sum.inr ())‖ₑ) + ‖γ₁‖ₑ) ^ θ
      = ((1 + a + ‖γ₁‖ₑ) + b + ‖α (Sum.inr ())‖ₑ) ^ θ := by ring_nf
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + b ^ θ + ‖α (Sum.inr ())‖ₑ ^ θ := rpow_add3_le h0 h1 _ _ _
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ +
          ((1 + ‖x1‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ + wR θ (vB α) γ₃ γ₅) :=
        add_le_add (add_le_add le_rfl hbw) (hs.trans (add_le_add (add_le_add hx1 hbw) hgw))
    _ ≤ _ := by
        calc (1 + a + ‖γ₁‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ +
              ((1 + ‖x1‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ + wR θ (vB α) γ₃ γ₅)
            ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ +
              ((1 + ‖x1‖ₑ) ^ θ + wR θ (vB α) γ₃ γ₅ + wR θ (vB α) γ₃ γ₅) +
                ((1 + ‖x0‖ₑ) ^ θ + (1 + ‖x1‖ₑ) ^ θ + 1) := le_self_add
          _ = _ := by ring

end Splits

end WaveTurbulence.ClassJR
