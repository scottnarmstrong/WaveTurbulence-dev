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

omit [Fintype ι₁] [Fintype ι₂] in
theorem vS_elim (a : ι₁ ⊕ ι₂ → ℝ) (s : Unit → ℝ) : (Sum.elim a s : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ)
    (Sum.inr ()) = s () := rfl

omit [Fintype ι₁] [Fintype ι₂] in
theorem vA_elim (a : ι₁ ⊕ ι₂ → ℝ) (s : Unit → ℝ) :
    vA (Sum.elim a s : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) = fun i => a (Sum.inl i) := rfl

omit [Fintype ι₁] [Fintype ι₂] in
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

section Norms

variable {θ A N₁ N₂ : ℝ} {R₁ : JSym ι₁} {R₂ : RSym ι₂}

theorem measurable_KMR : Measurable (Function.uncurry KMR) := by
  have hmap : Measurable fun p : (Fin 2 → ℝ) × (ℝ × ℝ) => ((p.1 0, p.2) : ℝ × (ℝ × ℝ)) :=
    ((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd
  have h1 := measurable_kerM.comp hmap
  have h2' : Measurable fun y : ℝ => (chiInvR y : ℂ) := contDiff_chiInvRc.continuous.measurable
  have h2 : Measurable fun p : (Fin 2 → ℝ) × (ℝ × ℝ) => (chiInvR (p.1 1) : ℂ) :=
    h2'.comp ((measurable_pi_apply 1).comp measurable_fst)
  have e : Function.uncurry KMR = fun p : (Fin 2 → ℝ) × (ℝ × ℝ) =>
      (Function.uncurry kerM ∘ fun p : (Fin 2 → ℝ) × (ℝ × ℝ) => ((p.1 0, p.2) : ℝ × (ℝ × ℝ))) p *
        (chiInvR (p.1 1) : ℂ) := by
    funext p
    simp only [Function.uncurry, KMR, Function.comp_apply]
  rw [e]
  exact h1.mul h2

/-- The shift of the `χ₀` piece in the layout `η = ((γ₂,γ₃),(γ₅,q))`. -/
@[expose] def bMR (η : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) : ℝ × ℝ :=
  (η.2.2.1, η.1.1 + η.1.2 - η.2.2.1)

/-- The shift of the first `χ_∞` piece. -/
@[expose] def bP1R (η : (ℝ × ℝ) × (ℝ × Unit)) : ℝ × ℝ := (η.1.1 + η.1.2, 0)

/-- The shift of the second `χ_∞` piece. -/
@[expose] def bP2R (η : (ℝ × ℝ) × (ℝ × Unit)) : ℝ × ℝ := (0, η.1.1 + η.1.2)

theorem RS_bounds (h0 : 0 ≤ θ) (h₂ : R₂.Bound θ A N₂) (j : ℕ) (c : ℕ) :
    (∫⁻ b, ∫⁻ γ : ℝ × (ℝ × ℝ), 1 * dnorm j R₂.m b γ ≤ gev N₂ A j) ∧
    (∫⁻ b, ∫⁻ γ : ℝ × (ℝ × ℝ), (c : ℝ≥0∞) * wR θ b γ.1 γ.2.2 * dnorm j R₂.m b γ ≤
      gev (c * N₂) A j) := by
  have hone : ∀ (b : ι₂ → ℝ) (γ : ℝ × (ℝ × ℝ)), 1 ≤ wR θ b γ.1 γ.2.2 := fun b γ => by
    unfold wR
    rcases h0.eq_or_lt with rfl | hθ
    · simp
    · exact ENNReal.one_le_rpow (le_add_right (le_add_right (le_add_right le_rfl))) hθ
  refine ⟨le_trans (lintegral_mono fun b => lintegral_mono fun γ =>
    mul_le_mul' (hone b γ) le_rfl) (h₂.norm j), ?_⟩
  have : ∫⁻ b, ∫⁻ γ : ℝ × (ℝ × ℝ), (c : ℝ≥0∞) * wR θ b γ.1 γ.2.2 * dnorm j R₂.m b γ =
      (c : ℝ≥0∞) * rNorm θ j R₂.m := by
    unfold rNorm
    simp_rw [mul_assoc]
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_congr fun b => ?_
    rw [lintegral_const_mul' _ _ (by simp)]
  rw [this, show (c : ℝ≥0∞) = ENNReal.ofReal c by simp]
  exact (mul_le_mul' le_rfl (h₂.norm j)).trans_eq (gev_mul_const _ (by positivity) j)

theorem gev_le_mul {N A' : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A') {c : ℝ} (hc : 1 ≤ c) (k : ℕ) :
    gev N A' k ≤ gev (c * N) A' k :=
  gev_mono (le_mul_of_one_le_left hN hc) hA le_rfl (by positivity) k

/-- **The `χ₀` piece of `J R`: weighted Gevrey bounds** (DH21 L1011–L1013). -/
theorem norm_piece_JR_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eJR (ℝ × ℝ) z).1.1 + (bMR (eJR (ℝ × ℝ) z).2).1) *
      dnorm k (tripleS R₁.m R₂.m KMR (LsJR R₁ R₂) (csJR (ℝ × ℝ))) α z ≤
        gev (3 * (16 * N₁ * (3 * N₂) * (16 * (CkM * IM) * CPhi))) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * (CkM * IM) * CPhi := by
    have := kerM_bound.1; have := IM_nonneg; have := CPhi_nonneg; positivity
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun a γ => wJ θ a γ.1, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => (3 : ℕ) * wR θ b γ.1 γ.2.2, fun _ _ => 1] with hw₂d
  set w₃ : Fin 3 → (Unit → ℝ) → (Fin 2 → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ _ => 1, fun _ _ _ => 1, fun _ x q => (1 + ‖x 1‖ₑ) + (1 + ‖q.1‖ₑ)] with hw₃d
  clear_value w₁ w₂ w₃
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_wJ θ
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
  have hw₃ : ∀ p, Measurable fun t : (Unit → ℝ) × ((Fin 2 → ℝ) × (ℝ × ℝ)) =>
      w₃ p t.1 t.2.1 t.2.2 := by
    intro p; subst hw₃d; fin_cases p
    · exact measurable_const
    · exact measurable_const
    · exact (measurable_const.add ((measurable_pi_apply 1).comp
        (measurable_fst.comp measurable_snd)).enorm).add
        (measurable_const.add ((measurable_fst.comp (measurable_snd.comp
          measurable_snd)).enorm))
  have hW : ∀ α z, wJ θ α ((eJR (ℝ × ℝ) z).1.1 + (bMR (eJR (ℝ × ℝ) z).2).1) ≤
      ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
        w₃ p (vS α) (formsV (LsJR R₁ R₂) (csJR (ℝ × ℝ)) α z) z.2.2 := fun α z => by
    simp only [eJR_apply, bMR, Fin.sum_univ_three, hw₁d, hw₂d, hw₃d, Matrix.cons_val, mul_one,
      one_mul, formsV_JR_one, Nat.cast_ofNat]
    exact wJ_split_JR_M h0 h1 h₂.sign h₂.bundle₁ α z.1.1 z.2.1.1 z.2.1.2.2 z.2.2.1
  have hΓ : ∀ p c (a : ι₁ ⊕ ι₂ → ℝ) (z₁ : ℝ × ℝ) (z₂ : ℝ × (ℝ × ℝ)), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      w₃ p s (formsV (LsJR R₁ R₂) (csJR (ℝ × ℝ)) (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ c (fun x => KMR x q)
          (formsV (LsJR R₁ R₂) (csJR (ℝ × ℝ)) (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤
          gev (16 * (CkM * IM) * CPhi) A c := by
    intro p c a z₁ z₂
    have hg := gamma_KMR_le h₂.sign
      (bundle R₂.y₂ (fun i => a (Sum.inr i)) - bundle R₁.y (fun i => a (Sum.inl i)) +
        (z₁.2 + z₂.1))
      (fun s q => formsV (LsJR R₁ R₂) (csJR (ℝ × ℝ)) (Sum.elim a s) (z₁, (z₂, q)))
      (fun s q => by rw [formsV_JR_zero]; rfl) c hA
    refine le_trans (lintegral_mono fun q => lintegral_mono fun s => ?_) hg
    subst hw₃d
    fin_cases p
    · simp only [Matrix.cons_val, Fin.zero_eta]
      exact mul_le_mul' (le_add_right (le_add_right le_rfl)) le_rfl
    · simp only [Matrix.cons_val, Fin.mk_one]
      exact mul_le_mul' (le_add_right (le_add_right le_rfl)) le_rfl
    · exact le_rfl
  have key := lintegral_tripleS_le (m₁ := R₁.m) (m₂ := R₂.m) (K := KMR) (Ls := LsJR R₁ R₂)
    (cs := csJR (ℝ × ℝ)) (isBundle_LsJR h₁ h₂) h₁.reg h₂.reg
    (fun q => (contDiff_prod2 (contDiff_kerM q) contDiff_chiInvRc))
    (measurable_KMR.stronglyMeasurable) (measurable_csJR _)
    (fun α z => wJ θ α ((eJR (ℝ × ℝ) z).1.1 + (bMR (eJR (ℝ × ℝ) z).2).1))
    w₁ w₂ w₃ hw₁ hw₂ hw₃ hW (fun _ c => gev (16 * (CkM * IM) * CPhi) A c) hΓ k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun _ j => gev (16 * (CkM * IM) * CPhi) A j) hN₁ (by positivity) hC hA0
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · exact (S_bounds h0 h₁ j).1
    · exact (S_bounds h0 h₁ j).2.1
    · exact (S_bounds h0 h₁ j).2.1
  · subst hw₂d; fin_cases p
    · exact (RS_bounds h0 h₂ j 3).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)
    · simpa using (RS_bounds h0 h₂ j 3).2
    · exact (RS_bounds h0 h₂ j 3).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)

theorem KPRn_iteratedFDeriv (c : ℕ) (x : Fin 2 → ℝ) (q : Unit) :
    ‖iteratedFDeriv ℝ c (fun x => KPRn x q) x‖ₑ = ‖iteratedFDeriv ℝ c (fun x => KPR x q) x‖ₑ := by
  rw [KPRn_eq, show (fun x => -prod2 phiR (fun y => (chiInvR y : ℂ)) x) =
    -(prod2 phiR fun y => (chiInvR y : ℂ)) from rfl, iteratedFDeriv_neg, Pi.neg_apply,
    enorm_neg, KPR_eq]

theorem measurable_KPR : Measurable (Function.uncurry KPR) := by
  have h' : Measurable fun y : ℝ => (chiInvR y : ℂ) := contDiff_chiInvRc.continuous.measurable
  have hp : Measurable phiR := contDiff_phiR.continuous.measurable
  have e : Function.uncurry KPR = fun p : (Fin 2 → ℝ) × Unit =>
      phiR (p.1 0) * (chiInvR (p.1 1) : ℂ) := by
    funext p; simp only [Function.uncurry, KPR]
  rw [e]
  exact (hp.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
    (h'.comp ((measurable_pi_apply 1).comp measurable_fst))

theorem measurable_KPRn : Measurable (Function.uncurry KPRn) := by
  have e : Function.uncurry KPRn = fun p : (Fin 2 → ℝ) × Unit => -Function.uncurry KPR p := by
    funext p; simp only [Function.uncurry, KPRn, KPR]
  rw [e]
  exact measurable_KPR.neg

/-- The `χ_∞` weight family of `J R` (pieces `p0`, `p1`, `p2`). -/
@[expose] noncomputable def w3P (θ : ℝ) : Fin 3 → (Unit → ℝ) → (Fin 2 → ℝ) → Unit → ℝ≥0∞ :=
  ![fun _ _ _ => 1, fun _ _ _ => 1,
    fun _ x _ => (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1]

theorem measurable_w3P (θ : ℝ) : ∀ p, Measurable fun t : (Unit → ℝ) × ((Fin 2 → ℝ) × Unit) =>
    w3P θ p t.1 t.2.1 t.2.2 := by
  intro p; fin_cases p
  · exact measurable_const
  · exact measurable_const
  · simp only [w3P]
    exact (((measurable_const.add ((measurable_pi_apply 0).comp
      (measurable_fst.comp measurable_snd)).enorm).pow_const _).add
        (measurable_const.mul ((measurable_const.add ((measurable_pi_apply 1).comp
          (measurable_fst.comp measurable_snd)).enorm).pow_const _))).add measurable_const

theorem w3P_le (θ : ℝ) (p : Fin 3) (s : Unit → ℝ) (x : Fin 2 → ℝ) (q : Unit) :
    w3P θ p s x q ≤ (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1 := by
  fin_cases p
  · exact le_add_self
  · exact le_add_self
  · exact le_rfl

/-- `Γ` for the `χ_∞` pieces, uniformly in the weight piece. -/
theorem gamma_P_JR (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₂ : R₂.Bound θ A N₂)
    (K : (Fin 2 → ℝ) → Unit → ℂ)
    (hK : ∀ c x q, ‖iteratedFDeriv ℝ c (fun x => K x q) x‖ₑ =
      ‖iteratedFDeriv ℝ c (fun x => KPR x q) x‖ₑ) :
    ∀ p c (a : ι₁ ⊕ ι₂ → ℝ) (z₁ : ℝ × ℝ) (z₂ : ℝ × (ℝ × ℝ)), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      w3P θ p s (formsV (LsJR R₁ R₂) (csJR Unit) (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ c (fun x => K x q)
          (formsV (LsJR R₁ R₂) (csJR Unit) (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤
          gev (16 * Cθ θ * (CPhi * CPhi)) A c := by
  intro p c a z₁ z₂
  have hg := gamma_KPR_le h0 h1 h₂.sign h₂.sign
    (bundle R₂.y₂ (fun i => a (Sum.inr i)) - bundle R₁.y (fun i => a (Sum.inl i)) +
      (z₁.2 + z₂.1)) (bundle R₂.y₁ (fun i => a (Sum.inr i)) + z₂.2.2)
    (fun s q => formsV (LsJR R₁ R₂) (csJR Unit) (Sum.elim a s) (z₁, (z₂, q)))
    (fun s q => by rw [formsV_JR_zero]; rfl) (fun s q => by rw [formsV_JR_one]; rfl) c hA
  refine le_trans (lintegral_mono fun q => lintegral_mono fun s => ?_) hg
  rw [hK]
  exact mul_le_mul' (w3P_le θ p _ _ _) le_rfl

/-- **The first `χ_∞` piece of `J R`: weighted Gevrey bounds** (DH21 L1014–L1017). -/
theorem norm_piece_JR_P1 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eJR Unit z).1.1 + (bP1R (eJR Unit z).2).1) *
      dnorm k (tripleS R₁.m R₂.m KPR (LsJR R₁ R₂) (csJR Unit)) α z ≤
        gev (3 * (16 * (2 * N₁) * (6 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun a γ => 2 * wJ θ a γ.1, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => (6 : ℕ) * wR θ b γ.1 γ.2.2, fun _ _ => 1] with hw₂d
  clear_value w₁ w₂
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wJ θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
  have hW : ∀ α z, wJ θ α ((eJR Unit z).1.1 + (bP1R (eJR Unit z).2).1) ≤
      ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
        w3P θ p (vS α) (formsV (LsJR R₁ R₂) (csJR Unit) α z) z.2.2 := fun α z => by
    simp only [eJR_apply, bP1R, Fin.sum_univ_three, hw₁d, hw₂d, w3P, Matrix.cons_val, mul_one,
      one_mul, formsV_JR_zero, formsV_JR_one, Nat.cast_ofNat]
    exact wJ_split_JR_P1 h0 h1.le h₂.sign h₁.bundle h₂.bundle₁ h₂.bundle₂ α z.1.1 z.1.2
      z.2.1.1 z.2.1.2.2
  have key := lintegral_tripleS_le (m₁ := R₁.m) (m₂ := R₂.m) (K := KPR) (Ls := LsJR R₁ R₂)
    (cs := csJR Unit) (isBundle_LsJR h₁ h₂) h₁.reg h₂.reg
    (fun q => (contDiff_prod2 contDiff_phiR contDiff_chiInvRc))
    (measurable_KPR.stronglyMeasurable) (measurable_csJR _)
    (fun α z => wJ θ α ((eJR Unit z).1.1 + (bP1R (eJR Unit z).2).1))
    w₁ w₂ (w3P θ) hw₁ hw₂ (measurable_w3P θ) hW (fun _ c => gev (16 * Cθ θ * (CPhi * CPhi)) A c)
    (gamma_P_JR h0 h1 hA h₂ KPR (fun _ _ _ => rfl)) k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun _ j => gev (16 * Cθ θ * (CPhi * CPhi)) A j) (by positivity) (by positivity) hC hA0
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · exact (S_bounds h0 h₁ j).2.2
    · exact (S_bounds h0 h₁ j).2.1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
    · exact (S_bounds h0 h₁ j).2.1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
  · subst hw₂d; fin_cases p
    · exact (RS_bounds h0 h₂ j 6).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)
    · simpa using (RS_bounds h0 h₂ j 6).2
    · exact (RS_bounds h0 h₂ j 6).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)

/-- **The second `χ_∞` piece of `J R`: weighted Gevrey bounds.** -/
theorem norm_piece_JR_P2 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eJR Unit z).1.1 + (bP2R (eJR Unit z).2).1) *
      dnorm k (tripleS R₁.m R₂.m KPRn (LsJR R₁ R₂) (csJR Unit)) α z ≤
        gev (3 * (16 * N₁ * (3 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun a γ => wJ θ a γ.1, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => (3 : ℕ) * wR θ b γ.1 γ.2.2, fun _ _ => 1] with hw₂d
  clear_value w₁ w₂
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_wJ θ
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
  have hW : ∀ α z, wJ θ α ((eJR Unit z).1.1 + (bP2R (eJR Unit z).2).1) ≤
      ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
        w3P θ p (vS α) (formsV (LsJR R₁ R₂) (csJR Unit) α z) z.2.2 := fun α z => by
    simp only [eJR_apply, bP2R, Fin.sum_univ_three, hw₁d, hw₂d, w3P, Matrix.cons_val, mul_one,
      one_mul, formsV_JR_one, Nat.cast_ofNat, add_zero]
    exact wJ_split_JR_P2 h0 h1.le h₂.sign h₂.bundle₁ α z.1.1 z.2.1.1 z.2.1.2.2 _
  have key := lintegral_tripleS_le (m₁ := R₁.m) (m₂ := R₂.m) (K := KPRn) (Ls := LsJR R₁ R₂)
    (cs := csJR Unit) (isBundle_LsJR h₁ h₂) h₁.reg h₂.reg
    (fun q => (contDiff_prod2 contDiff_phiR contDiff_chiInvRc).neg)
    (measurable_KPRn.stronglyMeasurable) (measurable_csJR _)
    (fun α z => wJ θ α ((eJR Unit z).1.1 + (bP2R (eJR Unit z).2).1))
    w₁ w₂ (w3P θ) hw₁ hw₂ (measurable_w3P θ) hW (fun _ c => gev (16 * Cθ θ * (CPhi * CPhi)) A c)
    (gamma_P_JR h0 h1 hA h₂ KPRn KPRn_iteratedFDeriv) k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun _ j => gev (16 * Cθ θ * (CPhi * CPhi)) A j) hN₁ (by positivity) hC hA0
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · exact (S_bounds h0 h₁ j).1
    · exact (S_bounds h0 h₁ j).2.1
    · exact (S_bounds h0 h₁ j).2.1
  · subst hw₂d; fin_cases p
    · exact (RS_bounds h0 h₂ j 3).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)
    · simpa using (RS_bounds h0 h₂ j 3).2
    · exact (RS_bounds h0 h₂ j 3).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)

end Norms

section Regular

variable {θ A N₁ N₂ : ℝ} {R₁ : JSym ι₁} {R₂ : RSym ι₂}

/-- A uniform bound for the derivatives of the `χ₀` coupling of `J R`. -/
@[expose] noncomputable def GMR (c : ℕ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * gM j q * gev CPhi Achi (c - j)

theorem measurable_GMR (c : ℕ) : Measurable (GMR c) :=
  Finset.measurable_sum _ fun j _ => (measurable_const.mul (measurable_gM j)).mul measurable_const

theorem enorm_iteratedFDeriv_KMR_le_GMR (c : ℕ) (x : Fin 2 → ℝ) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ c (fun x => KMR x q) x‖ₑ ≤ GMR c q := by
  rw [KMR_eq]
  refine (enorm_iteratedFDeriv_prod2_le (contDiff_kerM q) contDiff_chiInvRc c x).trans
    (Finset.sum_le_sum fun j _ => mul_le_mul' (mul_le_mul' le_rfl
      (enorm_iteratedDeriv_kerM_le j _ q)) ?_)
  refine (enorm_iteratedDeriv_chiInvRc_le (c - j) (x 1)).trans ?_
  refine mul_le_of_le_one_right bot_le ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ (by linarith [abs_nonneg (x 1)]))

theorem lintegral_GMR_ne_top (c : ℕ) : ∫⁻ q, GMR c q ≠ ⊤ := by
  unfold GMR
  rw [lintegral_finsetSum _ fun j _ => ((measurable_gM j).const_mul _).mul_const _]
  refine (ENNReal.sum_lt_top.2 fun j _ => ?_).ne
  rw [lintegral_mul_const _ ((measurable_gM j).const_mul _),
    lintegral_const_mul _ (measurable_gM j)]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp)
    (lt_of_le_of_lt (lintegral_gM_le j) (by simp [gev]))) (by simp [gev])

/-- A uniform bound for the derivatives of the `χ_∞` couplings of `J R`. -/
@[expose] noncomputable def GPR (c : ℕ) (_ : Unit) : ℝ≥0∞ :=
  ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * gev CPhi Achi j * gev CPhi Achi (c - j)

theorem enorm_iteratedFDeriv_KPR_le_GPR (c : ℕ) (x : Fin 2 → ℝ) (q : Unit) :
    ‖iteratedFDeriv ℝ c (fun x => KPR x q) x‖ₑ ≤ GPR c q := by
  rw [KPR_eq]
  have hle : ∀ y : ℝ, ENNReal.ofReal ((1 + |y|)⁻¹) ≤ 1 := fun y => by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ (by linarith [abs_nonneg y]))
  refine (enorm_iteratedFDeriv_prod2_le contDiff_phiR contDiff_chiInvRc c x).trans
    (Finset.sum_le_sum fun j _ => mul_le_mul' (mul_le_mul' le_rfl ?_) ?_)
  · exact (enorm_iteratedDeriv_phiR_le' j _).trans (mul_le_of_le_one_right bot_le (hle _))
  · exact (enorm_iteratedDeriv_chiInvRc_le _ _).trans
      (mul_le_of_le_one_right bot_le (hle _))

theorem lintegral_GPR_ne_top (c : ℕ) : ∫⁻ q, GPR c q ≠ ⊤ := by
  rw [show (volume : Measure Unit) = Measure.dirac () from rfl, lintegral_dirac]
  unfold GPR
  exact (ENNReal.sum_lt_top.2 fun j _ => ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp)
    (by simp [gev])) (by simp [gev])).ne

theorem symReg_piece_JR_M (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (tripleS R₁.m R₂.m KMR (LsJR R₁ R₂) (csJR (ℝ × ℝ))) :=
  tripleS_symReg (isBundle_LsJR h₁ h₂) h₁.reg h₂.reg
    (fun q => contDiff_prod2 (contDiff_kerM q) contDiff_chiInvRc)
    measurable_KMR.stronglyMeasurable (measurable_csJR _) GMR measurable_GMR
    enorm_iteratedFDeriv_KMR_le_GMR lintegral_GMR_ne_top

theorem symReg_piece_JR_P1 (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (tripleS R₁.m R₂.m KPR (LsJR R₁ R₂) (csJR Unit)) :=
  tripleS_symReg (isBundle_LsJR h₁ h₂) h₁.reg h₂.reg
    (fun _ => contDiff_prod2 contDiff_phiR contDiff_chiInvRc)
    measurable_KPR.stronglyMeasurable (measurable_csJR _) GPR (fun _ => measurable_const)
    enorm_iteratedFDeriv_KPR_le_GPR lintegral_GPR_ne_top

theorem symReg_piece_JR_P2 (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (tripleS R₁.m R₂.m KPRn (LsJR R₁ R₂) (csJR Unit)) :=
  tripleS_symReg (isBundle_LsJR h₁ h₂) h₁.reg h₂.reg
    (fun _ => (contDiff_prod2 contDiff_phiR contDiff_chiInvRc).neg)
    measurable_KPRn.stronglyMeasurable (measurable_csJR _) GPR (fun _ => measurable_const)
    (fun c x q => by rw [KPRn_iteratedFDeriv]; exact enorm_iteratedFDeriv_KPR_le_GPR c x q)
    lintegral_GPR_ne_top

theorem measurable_bMR : Measurable bMR := by unfold bMR; fun_prop
theorem measurable_bP1R : Measurable bP1R := by unfold bP1R; fun_prop
theorem measurable_bP2R : Measurable bP2R := by unfold bP2R; fun_prop

/-- The bundle `ℓ₁` of the `χ₀` and second `χ_∞` pieces of `J R`. -/
@[expose] def yJRL (R₁ : JSym ι₁) : (ι₁ ⊕ ι₂) ⊕ Unit → ℤ := y3 R₁.y 0 0

/-- The bundle `ℓ₃ + εα₁` of the first `χ_∞` piece of `J R`. -/
@[expose] def yJRR (R₂ : RSym ι₂) : (ι₁ ⊕ ι₂) ⊕ Unit → ℤ := y3 0 R₂.y₂ R₂.ε

theorem exists_piece_JR_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSym ((ι₁ ⊕ ι₂) ⊕ Unit),
      S.Bound θ A (3 * (16 * N₁ * (3 * N₂) * (16 * (CkM * IM) * CPhi))) ∧ ∀ α t s,
      S.kernel α t s = ∫ z, tripleS R₁.m R₂.m KMR (LsJR R₁ R₂) (csJR (ℝ × ℝ)) α z *
        jker (bundle (yJRL (ι₂ := ι₂) R₁) α)
          ((eJR (ℝ × ℝ) z).1.1 + (bMR (eJR (ℝ × ℝ) z).2).1)
          ((eJR (ℝ × ℝ) z).1.2 + (bMR (eJR (ℝ × ℝ) z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * (CkM * IM) * CPhi := by
    have := kerM_bound.1; have := IM_nonneg; have := CPhi_nonneg; positivity
  obtain ⟨S, -, hS, hk⟩ := JSym.ofGenE
    (isBundle_y3 h₁.bundle isBundle_zero (show |(0 : ℤ)| ≤ 1 by simp)) (symReg_piece_JR_M h₁ h₂)
    (eJR (ℝ × ℝ)) (measurePreserving_eJR _) measurable_bMR (by positivity)
    (norm_piece_JR_M h0 h1 hA h₁ h₂)
  exact ⟨S, hS, hk⟩

theorem exists_piece_JR_P1 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSym ((ι₁ ⊕ ι₂) ⊕ Unit),
      S.Bound θ A (3 * (16 * (2 * N₁) * (6 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))) ∧ ∀ α t s,
      S.kernel α t s = ∫ z, tripleS R₁.m R₂.m KPR (LsJR R₁ R₂) (csJR Unit) α z *
        jker (bundle (yJRR (ι₁ := ι₁) R₂) α)
          ((eJR Unit z).1.1 + (bP1R (eJR Unit z).2).1)
          ((eJR Unit z).1.2 + (bP1R (eJR Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  obtain ⟨S, -, hS, hk⟩ := JSym.ofGenE
    (isBundle_y3 isBundle_zero h₂.bundle₂ (abs_sign_le h₂.sign)) (symReg_piece_JR_P1 h₁ h₂)
    (eJR Unit) (measurePreserving_eJR _) measurable_bP1R (by positivity)
    (norm_piece_JR_P1 h0 h1 hA h₁ h₂)
  exact ⟨S, hS, hk⟩

theorem exists_piece_JR_P2 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSym ((ι₁ ⊕ ι₂) ⊕ Unit),
      S.Bound θ A (3 * (16 * N₁ * (3 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))) ∧ ∀ α t s,
      S.kernel α t s = ∫ z, tripleS R₁.m R₂.m KPRn (LsJR R₁ R₂) (csJR Unit) α z *
        jker (bundle (yJRL (ι₂ := ι₂) R₁) α)
          ((eJR Unit z).1.1 + (bP2R (eJR Unit z).2).1)
          ((eJR Unit z).1.2 + (bP2R (eJR Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  obtain ⟨S, -, hS, hk⟩ := JSym.ofGenE
    (isBundle_y3 h₁.bundle isBundle_zero (show |(0 : ℤ)| ≤ 1 by simp)) (symReg_piece_JR_P2 h₁ h₂)
    (eJR Unit) (measurePreserving_eJR _) measurable_bP2R (by positivity)
    (norm_piece_JR_P2 h0 h1 hA h₁ h₂)
  exact ⟨S, hS, hk⟩

end Regular

end WaveTurbulence.ClassJR
