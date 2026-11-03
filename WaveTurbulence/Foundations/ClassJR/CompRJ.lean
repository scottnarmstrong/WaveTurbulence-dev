/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Lemma54a

/-!
# DH21 Lemma 5.4, `R J`: the forms, the weight splits and the pieces

For `ℛ^{(1)} = ∫ m^{(1)} R_{ℓ₁+εα₁, ℓ₂+εα₁; γ₁,γ₂,γ₃}` and `𝒥^{(2)} = ∫ m^{(2)} J_{ℓ₃;γ₄,γ₅}`,
the composition kernel is `χ_∞(x₁)/x₁ · J_{ℓ₂+εα₁;γ₁,γ₂} J_{ℓ₃;γ₄,γ₅}` with
`x₁ = ℓ₁ + εα₁ + γ₃`, and the `J J` split gives three pieces with
`x₀ = ℓ₃ - ℓ₂ - εα₁ + γ₂ + γ₄`:

* `χ₀` piece: `kerM(x₀) χ_∞(x₁)/x₁`, bundle `ℓ₂ + εα₁`, `γ' = (γ₁ + σ, γ₂ + γ₄ + γ₅ - σ)`;
* `χ_∞` pieces: `±Φ(x₀) χ_∞(x₁)/x₁`, bundles `ℓ₃` and `ℓ₂ + εα₁`.

The layout of the integration variables is `z = ((γ₁,(γ₂,γ₃)),((γ₄,γ₅),q))`; the permutation
`eRJ` brings it to `((γ₁,γ₅),((γ₂,γ₄),(γ₃,q)))`, which has the shape of the `J R` layout, so the
shifts `bMR`, `bP1R`, `bP2R` and the coupling bounds of `J R` are reused. The two forms carry
opposite signs `∓ε` of the special variable, which is why the coupling bounds of
`WaveTurbulence.ClassJR.CompJR` allow independent signs.

In the weight of the composed operator, `|α₁|^θ` is controlled through `x₁ = ℓ₁ + εα₁ + γ₃`
by the class `R` weight of `m^{(1)}` (DH21 L1018: "the proof for `ℛ𝒥` is similar").
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section Equiv

variable (Q : Type*) [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- `((γ₁,(γ₂,γ₃)),((γ₄,γ₅),q)) ↦ ((γ₁,γ₅),((γ₂,γ₄),(γ₃,q)))`. -/
@[expose] def eRJ : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Q) ≃ᵐ (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × Q)) where
  toFun z := ((z.1.1, z.2.1.2), ((z.1.2.1, z.2.1.1), (z.1.2.2, z.2.2)))
  invFun z := ((z.1.1, (z.2.1.1, z.2.2.1)), ((z.2.1.2, z.1.2), z.2.2.2))
  left_inv z := rfl
  right_inv z := rfl
  measurable_toFun := by
    change Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Q) =>
      ((z.1.1, z.2.1.2), ((z.1.2.1, z.2.1.1), (z.1.2.2, z.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × Q)) =>
      ((z.1.1, (z.2.1.1, z.2.2.1)), ((z.2.1.2, z.1.2), z.2.2.2))
    fun_prop

omit [SFinite (volume : Measure Q)] in
@[simp] theorem eRJ_apply (z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Q)) :
    eRJ Q z = ((z.1.1, z.2.1.2), ((z.1.2.1, z.2.1.1), (z.1.2.2, z.2.2))) := rfl

theorem measurePreserving_eRJ : MeasurePreserving (eRJ Q) := by
  have g1 : MeasurePreserving (Prod.map
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ)).symm (id : (ℝ × ℝ) × Q → _)) :=
    MeasurePreserving.prod volume_preserving_prodAssoc.symm (MeasurePreserving.id volume)
  have g2 := volume_preserving_prodAssoc (α₁ := ℝ × ℝ) (β₁ := ℝ) (γ₁ := (ℝ × ℝ) × Q)
  have h1 := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ × ℝ) (γ₁ := Q)).symm
  have h2 : MeasurePreserving (Prod.map (Prod.swap : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ)
      (id : Q → Q)) :=
    MeasurePreserving.prod (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (ℝ × ℝ)))) (MeasurePreserving.id volume)
  have h3 := volume_preserving_prodAssoc (α₁ := ℝ × ℝ) (β₁ := ℝ) (γ₁ := Q)
  have hh := h3.comp (h2.comp h1)
  have g3 : MeasurePreserving (Prod.map (id : ℝ × ℝ → ℝ × ℝ)
      ((MeasurableEquiv.prodAssoc (α := ℝ × ℝ) (β := ℝ) (γ := Q)) ∘
        Prod.map (Prod.swap : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ) (id : Q → Q) ∘
          (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ × ℝ) (γ := Q)).symm)) :=
    MeasurePreserving.prod (MeasurePreserving.id volume) hh
  have := (measurePreserving_eJJ (ℝ × Q)).comp (g3.comp (g2.comp g1))
  convert this using 1
  funext z
  rfl

end Equiv

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

theorem sign_neg {e : ℤ} (he : e = 1 ∨ e = -1) : -e = 1 ∨ -e = -1 := by
  rcases he with rfl | rfl <;> simp

section Data

/-- The two forms `x₀ = ℓ₃ - ℓ₂ - εα₁ (+ γ₂ + γ₄)` and `x₁ = ℓ₁ + εα₁ (+ γ₃)`. -/
@[expose] def LsRJ (R₁ : RSym ι₁) (R₂ : JSym ι₂) : Fin 2 → (ι₁ ⊕ ι₂) ⊕ Unit → ℤ :=
  ![y3 (fun i => -R₁.y₂ i) R₂.y (-R₁.ε), y3 R₁.y₁ 0 R₁.ε]

/-- The constant parts `γ₂ + γ₄` and `γ₃` of the two forms. -/
@[expose] def csRJ (Q : Type*) : Fin 2 → (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Q) → ℝ :=
  ![fun z => z.1.2.1 + z.2.1.1, fun z => z.1.2.2]

variable {R₁ : RSym ι₁} {R₂ : JSym ι₂}

theorem isBundle_LsRJ {θ A N₁ N₂ : ℝ} (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    ∀ r, IsBundle (LsRJ R₁ R₂ r) := by
  intro r; fin_cases r
  · exact isBundle_y3 (isBundle_neg h₁.bundle₂) h₂.bundle (abs_sign_le (sign_neg h₁.sign))
  · exact isBundle_y3 h₁.bundle₁ isBundle_zero (abs_sign_le h₁.sign)

theorem measurable_csRJ (Q : Type*) [MeasurableSpace Q] : ∀ r, Measurable (csRJ Q r) := by
  intro r; fin_cases r
  · simp only [csRJ]; exact (measurable_fst.comp (measurable_snd.comp measurable_fst)).add
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
  · simp only [csRJ]
    exact measurable_snd.comp (measurable_snd.comp measurable_fst)

theorem formsV_RJ_zero {Q : Type*} (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ)
    (z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Q)) :
    formsV (LsRJ R₁ R₂) (csRJ Q) α z 0 =
      bundle R₂.y (vB α) - bundle R₁.y₂ (vA α) + (z.1.2.1 + z.2.1.1) +
        ((-R₁.ε : ℤ) : ℝ) * α (Sum.inr ()) := by
  simp only [formsV, LsRJ, csRJ, Matrix.cons_val, bundle_y3]
  have : bundle (fun i => -R₁.y₂ i) (vA α) = -bundle R₁.y₂ (vA α) := by
    simp [bundle, Finset.sum_neg_distrib]
  rw [this]
  ring

theorem formsV_RJ_one {Q : Type*} (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ)
    (z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Q)) :
    formsV (LsRJ R₁ R₂) (csRJ Q) α z 1 =
      bundle R₁.y₁ (vA α) + z.1.2.2 + R₁.ε * α (Sum.inr ()) := by
  simp only [formsV, LsRJ, csRJ, Matrix.cons_val, bundle_y3]
  have : bundle (0 : ι₂ → ℤ) (vB α) = 0 := by simp [bundle]
  rw [this]
  ring

end Data

section Splits

variable {θ : ℝ} {ε : ℤ}

/-- The `J` weight is dominated by the `R` weight. -/
theorem wJ_le_wR {ι : Type*} [Fintype ι] (h0 : 0 ≤ θ) (b : ι → ℝ) (γ₁ γ₃ : ℝ) :
    wJ θ b γ₁ ≤ wR θ b γ₁ γ₃ :=
  rpow_mono' h0 le_self_add

/-- The weight split of the `χ₀` piece of `R J`. -/
theorem wJ_split_RJ_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {d : ι₁ → ℤ}
    (hd : IsBundle d) (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) (γ₁ γ₃ γ₄ σ : ℝ) :
    wJ θ α (γ₁ + σ) ≤ 3 * wR θ (vA α) γ₁ γ₃ + wJ θ (vB α) γ₄ +
      ((1 + ‖bundle d (vA α) + γ₃ + ε * α (Sum.inr ())‖ₑ) + (1 + ‖σ‖ₑ)) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set b := ∑ i, ‖vB α i‖ₑ
  set x1 := bundle d (vA α) + γ₃ + ε * α (Sum.inr ())
  have hs := special_rpow_le h0 h1 hε (α (Sum.inr ())) (bundle d (vA α)) γ₃ (abs_bundle_le hd _)
  have haw : a ^ θ ≤ wR θ (vA α) γ₁ γ₃ := sum_rpow_le_wR h0 _ _ _
  have hgw : ‖γ₃‖ₑ ^ θ ≤ wR θ (vA α) γ₁ γ₃ := enorm_rpow_le_wR h0 _ _ _
  have hbw : b ^ θ ≤ wJ θ (vB α) γ₄ := sum_rpow_le_wJ h0 _ _
  have h1w : (1 + a + ‖γ₁‖ₑ) ^ θ ≤ wR θ (vA α) γ₁ γ₃ := wJ_le_wR h0 _ _ _
  have hL : wJ θ α (γ₁ + σ) = (1 + ∑ j, ‖α j‖ₑ + ‖γ₁ + σ‖ₑ) ^ θ := rfl
  rw [hL, sum_enorm_y3]
  calc (1 + (a + b + ‖α (Sum.inr ())‖ₑ) + ‖γ₁ + σ‖ₑ) ^ θ
      ≤ ((1 + a + ‖γ₁‖ₑ) + b + ‖α (Sum.inr ())‖ₑ + ‖σ‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + b + ‖α (Sum.inr ())‖ₑ) + ‖γ₁ + σ‖ₑ
            ≤ 1 + (a + b + ‖α (Sum.inr ())‖ₑ) + (‖γ₁‖ₑ + ‖σ‖ₑ) := by
              gcongr; exact enorm_add_le _ _
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + b ^ θ + ‖α (Sum.inr ())‖ₑ ^ θ + ‖σ‖ₑ ^ θ :=
        rpow_add4_le h0 h1 _ _ _ _
    _ ≤ wR θ (vA α) γ₁ γ₃ + wJ θ (vB α) γ₄ +
          (‖x1‖ₑ ^ θ + wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) + (1 + ‖σ‖ₑ) :=
        add_le_add (add_le_add (add_le_add h1w hbw)
          (hs.trans (add_le_add (add_le_add le_rfl haw) hgw))) (rpow_le_one_add h0 h1 _)
    _ ≤ 3 * wR θ (vA α) γ₁ γ₃ + wJ θ (vB α) γ₄ + ((1 + ‖x1‖ₑ) + (1 + ‖σ‖ₑ)) := by
        have := rpow_le_one_add h0 h1 ‖x1‖ₑ
        calc wR θ (vA α) γ₁ γ₃ + wJ θ (vB α) γ₄ +
              (‖x1‖ₑ ^ θ + wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) + (1 + ‖σ‖ₑ)
            ≤ wR θ (vA α) γ₁ γ₃ + wJ θ (vB α) γ₄ +
              ((1 + ‖x1‖ₑ) + wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) + (1 + ‖σ‖ₑ) := by gcongr
          _ = _ := by ring

/-- The weight split of the first `χ_∞` piece of `R J` (`γ₁' = γ₁ + γ₂ + γ₄`). -/
theorem wJ_split_RJ_P1 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {y : ι₂ → ℤ}
    {d ph : ι₁ → ℤ} (hy : IsBundle y) (hd : IsBundle d) (hph : IsBundle ph)
    (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) (γ₁ γ₂ γ₃ γ₄ : ℝ) :
    wJ θ α (γ₁ + (γ₂ + γ₄)) ≤ 6 * wR θ (vA α) γ₁ γ₃ + 2 * wJ θ (vB α) γ₄ +
      ((1 + ‖bundle y (vB α) - bundle ph (vA α) + (γ₂ + γ₄) +
          ((-ε : ℤ) : ℝ) * α (Sum.inr ())‖ₑ) ^ θ +
        2 * (1 + ‖bundle d (vA α) + γ₃ + ε * α (Sum.inr ())‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set b := ∑ i, ‖vB α i‖ₑ
  set e := ‖α (Sum.inr ())‖ₑ
  set x0 := bundle y (vB α) - bundle ph (vA α) + (γ₂ + γ₄) + ((-ε : ℤ) : ℝ) * α (Sum.inr ())
  set x1 := bundle d (vA α) + γ₃ + ε * α (Sum.inr ())
  have hε1 : ‖((-ε : ℤ) : ℝ)‖ₑ = 1 := by rcases hε with rfl | rfl <;> simp
  have hx : ‖γ₂ + γ₄‖ₑ ≤ ‖x0‖ₑ + b + a + e := by
    have : γ₂ + γ₄ = x0 + -bundle y (vB α) + bundle ph (vA α) +
        -(((-ε : ℤ) : ℝ) * α (Sum.inr ())) := by
      simp only [x0]; ring
    rw [this]
    refine (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans
      (add_le_add ((enorm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)) ?_)
    · rw [enorm_neg]; exact abs_bundle_le hy _
    · exact abs_bundle_le hph _
    · rw [enorm_neg, enorm_mul, hε1, one_mul]
  have hs := special_rpow_le h0 h1 hε (α (Sum.inr ())) (bundle d (vA α)) γ₃ (abs_bundle_le hd _)
  have haw : a ^ θ ≤ wR θ (vA α) γ₁ γ₃ := sum_rpow_le_wR h0 _ _ _
  have hgw : ‖γ₃‖ₑ ^ θ ≤ wR θ (vA α) γ₁ γ₃ := enorm_rpow_le_wR h0 _ _ _
  have hbw : b ^ θ ≤ wJ θ (vB α) γ₄ := sum_rpow_le_wJ h0 _ _
  have h1w : (1 + a + ‖γ₁‖ₑ) ^ θ ≤ wR θ (vA α) γ₁ γ₃ := wJ_le_wR h0 _ _ _
  have h2 : ∀ u : ℝ≥0∞, (u + u) ^ θ ≤ 2 * u ^ θ := fun u =>
    (rpow_add_le h0 h1 u u).trans_eq (two_mul _).symm
  have hx0 : ‖x0‖ₑ ^ θ ≤ (1 + ‖x0‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hx1 : ‖x1‖ₑ ^ θ ≤ (1 + ‖x1‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hL : wJ θ α (γ₁ + (γ₂ + γ₄)) = (1 + ∑ j, ‖α j‖ₑ + ‖γ₁ + (γ₂ + γ₄)‖ₑ) ^ θ := rfl
  rw [hL, sum_enorm_y3]
  calc (1 + (a + b + e) + ‖γ₁ + (γ₂ + γ₄)‖ₑ) ^ θ
      ≤ (((1 + a + ‖γ₁‖ₑ) + a) + (b + b) + (e + e) + ‖x0‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + b + e) + ‖γ₁ + (γ₂ + γ₄)‖ₑ ≤ 1 + (a + b + e) + (‖γ₁‖ₑ + ‖γ₂ + γ₄‖ₑ) := by
              gcongr; exact enorm_add_le _ _
          _ ≤ 1 + (a + b + e) + (‖γ₁‖ₑ + (‖x0‖ₑ + b + a + e)) := by gcongr
          _ = _ := by ring
    _ ≤ ((1 + a + ‖γ₁‖ₑ) + a) ^ θ + (b + b) ^ θ + (e + e) ^ θ + ‖x0‖ₑ ^ θ :=
        rpow_add4_le h0 h1 _ _ _ _
    _ ≤ ((1 + a + ‖γ₁‖ₑ) ^ θ + a ^ θ) + 2 * b ^ θ + 2 * e ^ θ + ‖x0‖ₑ ^ θ :=
        add_le_add (add_le_add (add_le_add (rpow_add_le h0 h1 _ _) (h2 b)) (h2 e)) le_rfl
    _ ≤ (wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) + 2 * wJ θ (vB α) γ₄ +
          2 * (‖x1‖ₑ ^ θ + wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) + (1 + ‖x0‖ₑ) ^ θ := by
        gcongr
        exact hs.trans (add_le_add (add_le_add le_rfl haw) hgw)
    _ ≤ _ := by
        calc (wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) + 2 * wJ θ (vB α) γ₄ +
              2 * (‖x1‖ₑ ^ θ + wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) + (1 + ‖x0‖ₑ) ^ θ
            ≤ (wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) + 2 * wJ θ (vB α) γ₄ +
              2 * ((1 + ‖x1‖ₑ) ^ θ + wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) +
                ((1 + ‖x0‖ₑ) ^ θ + 1) := by gcongr; exact le_self_add
          _ = _ := by ring

/-- The weight split of the second `χ_∞` piece of `R J` (`γ₁' = γ₁`). -/
theorem wJ_split_RJ_P2 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1) {d : ι₁ → ℤ}
    (hd : IsBundle d) (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) (γ₁ γ₃ γ₄ : ℝ) (x0 : ℝ) :
    wJ θ α γ₁ ≤ 3 * wR θ (vA α) γ₁ γ₃ + wJ θ (vB α) γ₄ +
      ((1 + ‖x0‖ₑ) ^ θ + 2 * (1 + ‖bundle d (vA α) + γ₃ + ε * α (Sum.inr ())‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set b := ∑ i, ‖vB α i‖ₑ
  set x1 := bundle d (vA α) + γ₃ + ε * α (Sum.inr ())
  have hs := special_rpow_le h0 h1 hε (α (Sum.inr ())) (bundle d (vA α)) γ₃ (abs_bundle_le hd _)
  have haw : a ^ θ ≤ wR θ (vA α) γ₁ γ₃ := sum_rpow_le_wR h0 _ _ _
  have hgw : ‖γ₃‖ₑ ^ θ ≤ wR θ (vA α) γ₁ γ₃ := enorm_rpow_le_wR h0 _ _ _
  have hbw : b ^ θ ≤ wJ θ (vB α) γ₄ := sum_rpow_le_wJ h0 _ _
  have h1w : (1 + a + ‖γ₁‖ₑ) ^ θ ≤ wR θ (vA α) γ₁ γ₃ := wJ_le_wR h0 _ _ _
  have hx1 : ‖x1‖ₑ ^ θ ≤ (1 + ‖x1‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hL : wJ θ α γ₁ = (1 + ∑ j, ‖α j‖ₑ + ‖γ₁‖ₑ) ^ θ := rfl
  rw [hL, sum_enorm_y3]
  calc (1 + (a + b + ‖α (Sum.inr ())‖ₑ) + ‖γ₁‖ₑ) ^ θ
      = ((1 + a + ‖γ₁‖ₑ) + b + ‖α (Sum.inr ())‖ₑ) ^ θ := by ring_nf
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + b ^ θ + ‖α (Sum.inr ())‖ₑ ^ θ := rpow_add3_le h0 h1 _ _ _
    _ ≤ wR θ (vA α) γ₁ γ₃ + wJ θ (vB α) γ₄ +
          ((1 + ‖x1‖ₑ) ^ θ + wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) :=
        add_le_add (add_le_add h1w hbw) (hs.trans (add_le_add (add_le_add hx1 haw) hgw))
    _ ≤ _ := by
        calc wR θ (vA α) γ₁ γ₃ + wJ θ (vB α) γ₄ +
              ((1 + ‖x1‖ₑ) ^ θ + wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃)
            ≤ wR θ (vA α) γ₁ γ₃ + wJ θ (vB α) γ₄ +
              ((1 + ‖x1‖ₑ) ^ θ + wR θ (vA α) γ₁ γ₃ + wR θ (vA α) γ₁ γ₃) +
                ((1 + ‖x0‖ₑ) ^ θ + (1 + ‖x1‖ₑ) ^ θ + 1) := le_self_add
          _ = _ := by ring

end Splits

section Norms

variable {θ A N₁ N₂ : ℝ} {R₁ : RSym ι₁} {R₂ : JSym ι₂}

/-- **The `χ₀` piece of `R J`: weighted Gevrey bounds.** -/
theorem norm_piece_RJ_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eRJ (ℝ × ℝ) z).1.1 + (bMR (eRJ (ℝ × ℝ) z).2).1) *
      dnorm k (tripleS R₁.m R₂.m KMR (LsRJ R₁ R₂) (csRJ (ℝ × ℝ))) α z ≤
        gev (3 * (16 * (3 * N₁) * N₂ * (16 * (CkM * IM) * CPhi))) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * (CkM * IM) * CPhi := by
    have := kerM_bound.1; have := IM_nonneg; have := CPhi_nonneg; positivity
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun a γ => (3 : ℕ) * wR θ a γ.1 γ.2.2, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => wJ θ b γ.1, fun _ _ => 1] with hw₂d
  set w₃ : Fin 3 → (Unit → ℝ) → (Fin 2 → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ _ => 1, fun _ _ _ => 1, fun _ x q => (1 + ‖x 1‖ₑ) + (1 + ‖q.1‖ₑ)] with hw₃d
  clear_value w₁ w₂ w₃
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_wJ θ
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
  have hW : ∀ α z, wJ θ α ((eRJ (ℝ × ℝ) z).1.1 + (bMR (eRJ (ℝ × ℝ) z).2).1) ≤
      ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
        w₃ p (vS α) (formsV (LsRJ R₁ R₂) (csRJ (ℝ × ℝ)) α z) z.2.2 := fun α z => by
    simp only [eRJ_apply, bMR, Fin.sum_univ_three, hw₁d, hw₂d, hw₃d, Matrix.cons_val, mul_one,
      one_mul, formsV_RJ_one, Nat.cast_ofNat]
    exact wJ_split_RJ_M h0 h1 h₁.sign h₁.bundle₁ α z.1.1 z.1.2.2 z.2.1.1 z.2.2.1
  have hΓ : ∀ p c (a : ι₁ ⊕ ι₂ → ℝ) (z₁ : ℝ × (ℝ × ℝ)) (z₂ : ℝ × ℝ), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      w₃ p s (formsV (LsRJ R₁ R₂) (csRJ (ℝ × ℝ)) (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ c (fun x => KMR x q)
          (formsV (LsRJ R₁ R₂) (csRJ (ℝ × ℝ)) (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤
          gev (16 * (CkM * IM) * CPhi) A c := by
    intro p c a z₁ z₂
    have hg := gamma_KMR_le (sign_neg h₁.sign)
      (bundle R₂.y (fun i => a (Sum.inr i)) - bundle R₁.y₂ (fun i => a (Sum.inl i)) +
        (z₁.2.1 + z₂.1))
      (fun s q => formsV (LsRJ R₁ R₂) (csRJ (ℝ × ℝ)) (Sum.elim a s) (z₁, (z₂, q)))
      (fun s q => by rw [formsV_RJ_zero]; rfl) c hA
    refine le_trans (lintegral_mono fun q => lintegral_mono fun s => ?_) hg
    subst hw₃d
    fin_cases p
    · simp only [Matrix.cons_val, Fin.zero_eta]
      exact mul_le_mul' (le_add_right (le_add_right le_rfl)) le_rfl
    · simp only [Matrix.cons_val, Fin.mk_one]
      exact mul_le_mul' (le_add_right (le_add_right le_rfl)) le_rfl
    · exact le_rfl
  have key := lintegral_tripleS_le (m₁ := R₁.m) (m₂ := R₂.m) (K := KMR) (Ls := LsRJ R₁ R₂)
    (cs := csRJ (ℝ × ℝ)) (isBundle_LsRJ h₁ h₂) h₁.reg h₂.reg
    (fun q => (contDiff_prod2 (contDiff_kerM q) contDiff_chiInvRc))
    (measurable_KMR.stronglyMeasurable) (measurable_csRJ _)
    (fun α z => wJ θ α ((eRJ (ℝ × ℝ) z).1.1 + (bMR (eRJ (ℝ × ℝ) z).2).1))
    w₁ w₂ w₃ hw₁ hw₂ hw₃ hW (fun _ c => gev (16 * (CkM * IM) * CPhi) A c) hΓ k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun _ j => gev (16 * (CkM * IM) * CPhi) A j) (by positivity) hN₂ hC hA0
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · simpa using (RS_bounds h0 h₁ j 3).2
    · exact (RS_bounds h0 h₁ j 3).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
    · exact (RS_bounds h0 h₁ j 3).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
  · subst hw₂d; fin_cases p
    · exact (S_bounds h0 h₂ j).2.1
    · exact (S_bounds h0 h₂ j).1
    · exact (S_bounds h0 h₂ j).2.1

/-- `Γ` for the `χ_∞` pieces of `R J`, uniformly in the weight piece. -/
theorem gamma_P_RJ (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (K : (Fin 2 → ℝ) → Unit → ℂ)
    (hK : ∀ c x q, ‖iteratedFDeriv ℝ c (fun x => K x q) x‖ₑ =
      ‖iteratedFDeriv ℝ c (fun x => KPR x q) x‖ₑ) :
    ∀ p c (a : ι₁ ⊕ ι₂ → ℝ) (z₁ : ℝ × (ℝ × ℝ)) (z₂ : ℝ × ℝ), ∫⁻ q, ∫⁻ s : Unit → ℝ,
      w3P θ p s (formsV (LsRJ R₁ R₂) (csRJ Unit) (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ c (fun x => K x q)
          (formsV (LsRJ R₁ R₂) (csRJ Unit) (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤
          gev (16 * Cθ θ * (CPhi * CPhi)) A c := by
  intro p c a z₁ z₂
  have hg := gamma_KPR_le h0 h1 (sign_neg h₁.sign) h₁.sign
    (bundle R₂.y (fun i => a (Sum.inr i)) - bundle R₁.y₂ (fun i => a (Sum.inl i)) +
      (z₁.2.1 + z₂.1)) (bundle R₁.y₁ (fun i => a (Sum.inl i)) + z₁.2.2)
    (fun s q => formsV (LsRJ R₁ R₂) (csRJ Unit) (Sum.elim a s) (z₁, (z₂, q)))
    (fun s q => by rw [formsV_RJ_zero]; rfl) (fun s q => by rw [formsV_RJ_one]; rfl) c hA
  refine le_trans (lintegral_mono fun q => lintegral_mono fun s => ?_) hg
  rw [hK]
  exact mul_le_mul' (w3P_le θ p _ _ _) le_rfl

/-- **The first `χ_∞` piece of `R J`: weighted Gevrey bounds.** -/
theorem norm_piece_RJ_P1 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eRJ Unit z).1.1 + (bP1R (eRJ Unit z).2).1) *
      dnorm k (tripleS R₁.m R₂.m KPR (LsRJ R₁ R₂) (csRJ Unit)) α z ≤
        gev (3 * (16 * (6 * N₁) * (2 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun a γ => (6 : ℕ) * wR θ a γ.1 γ.2.2, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => 2 * wJ θ b γ.1, fun _ _ => 1] with hw₂d
  clear_value w₁ w₂
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_const.mul (measurable_wJ θ)
    · exact measurable_const
  have hW : ∀ α z, wJ θ α ((eRJ Unit z).1.1 + (bP1R (eRJ Unit z).2).1) ≤
      ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
        w3P θ p (vS α) (formsV (LsRJ R₁ R₂) (csRJ Unit) α z) z.2.2 := fun α z => by
    simp only [eRJ_apply, bP1R, Fin.sum_univ_three, hw₁d, hw₂d, w3P, Matrix.cons_val, mul_one,
      one_mul, formsV_RJ_zero, formsV_RJ_one, Nat.cast_ofNat]
    exact wJ_split_RJ_P1 h0 h1.le h₁.sign h₂.bundle h₁.bundle₁ h₁.bundle₂ α z.1.1 z.1.2.1
      z.1.2.2 z.2.1.1
  have key := lintegral_tripleS_le (m₁ := R₁.m) (m₂ := R₂.m) (K := KPR) (Ls := LsRJ R₁ R₂)
    (cs := csRJ Unit) (isBundle_LsRJ h₁ h₂) h₁.reg h₂.reg
    (fun q => (contDiff_prod2 contDiff_phiR contDiff_chiInvRc))
    (measurable_KPR.stronglyMeasurable) (measurable_csRJ _)
    (fun α z => wJ θ α ((eRJ Unit z).1.1 + (bP1R (eRJ Unit z).2).1))
    w₁ w₂ (w3P θ) hw₁ hw₂ (measurable_w3P θ) hW (fun _ c => gev (16 * Cθ θ * (CPhi * CPhi)) A c)
    (gamma_P_RJ h0 h1 hA h₁ KPR (fun _ _ _ => rfl)) k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun _ j => gev (16 * Cθ θ * (CPhi * CPhi)) A j) (by positivity) (by positivity) hC hA0
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · simpa using (RS_bounds h0 h₁ j 6).2
    · exact (RS_bounds h0 h₁ j 6).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
    · exact (RS_bounds h0 h₁ j 6).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
  · subst hw₂d; fin_cases p
    · exact (S_bounds h0 h₂ j).2.1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)
    · exact (S_bounds h0 h₂ j).2.2
    · exact (S_bounds h0 h₂ j).2.1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)

/-- **The second `χ_∞` piece of `R J`: weighted Gevrey bounds.** -/
theorem norm_piece_RJ_P2 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eRJ Unit z).1.1 + (bP2R (eRJ Unit z).2).1) *
      dnorm k (tripleS R₁.m R₂.m KPRn (LsRJ R₁ R₂) (csRJ Unit)) α z ≤
        gev (3 * (16 * (3 * N₁) * N₂ * (16 * Cθ θ * (CPhi * CPhi)))) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun a γ => (3 : ℕ) * wR θ a γ.1 γ.2.2, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => wJ θ b γ.1, fun _ _ => 1] with hw₂d
  clear_value w₁ w₂
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_wJ θ
    · exact measurable_const
  have hW : ∀ α z, wJ θ α ((eRJ Unit z).1.1 + (bP2R (eRJ Unit z).2).1) ≤
      ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
        w3P θ p (vS α) (formsV (LsRJ R₁ R₂) (csRJ Unit) α z) z.2.2 := fun α z => by
    simp only [eRJ_apply, bP2R, Fin.sum_univ_three, hw₁d, hw₂d, w3P, Matrix.cons_val, mul_one,
      one_mul, formsV_RJ_one, Nat.cast_ofNat, add_zero]
    exact wJ_split_RJ_P2 h0 h1.le h₁.sign h₁.bundle₁ α z.1.1 z.1.2.2 z.2.1.1 _
  have key := lintegral_tripleS_le (m₁ := R₁.m) (m₂ := R₂.m) (K := KPRn) (Ls := LsRJ R₁ R₂)
    (cs := csRJ Unit) (isBundle_LsRJ h₁ h₂) h₁.reg h₂.reg
    (fun q => (contDiff_prod2 contDiff_phiR contDiff_chiInvRc).neg)
    (measurable_KPRn.stronglyMeasurable) (measurable_csRJ _)
    (fun α z => wJ θ α ((eRJ Unit z).1.1 + (bP2R (eRJ Unit z).2).1))
    w₁ w₂ (w3P θ) hw₁ hw₂ (measurable_w3P θ) hW (fun _ c => gev (16 * Cθ θ * (CPhi * CPhi)) A c)
    (gamma_P_RJ h0 h1 hA h₁ KPRn KPRn_iteratedFDeriv) k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun _ j => gev (16 * Cθ θ * (CPhi * CPhi)) A j) (by positivity) hN₂ hC hA0
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · simpa using (RS_bounds h0 h₁ j 3).2
    · exact (RS_bounds h0 h₁ j 3).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
    · exact (RS_bounds h0 h₁ j 3).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
  · subst hw₂d; fin_cases p
    · exact (S_bounds h0 h₂ j).2.1
    · exact (S_bounds h0 h₂ j).1
    · exact (S_bounds h0 h₂ j).2.1

end Norms

section Regular

variable {θ A N₁ N₂ : ℝ} {R₁ : RSym ι₁} {R₂ : JSym ι₂}

theorem symReg_piece_RJ_M (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (tripleS R₁.m R₂.m KMR (LsRJ R₁ R₂) (csRJ (ℝ × ℝ))) :=
  tripleS_symReg (isBundle_LsRJ h₁ h₂) h₁.reg h₂.reg
    (fun q => contDiff_prod2 (contDiff_kerM q) contDiff_chiInvRc)
    measurable_KMR.stronglyMeasurable (measurable_csRJ _) GMR measurable_GMR
    enorm_iteratedFDeriv_KMR_le_GMR lintegral_GMR_ne_top

theorem symReg_piece_RJ_P1 (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (tripleS R₁.m R₂.m KPR (LsRJ R₁ R₂) (csRJ Unit)) :=
  tripleS_symReg (isBundle_LsRJ h₁ h₂) h₁.reg h₂.reg
    (fun _ => contDiff_prod2 contDiff_phiR contDiff_chiInvRc)
    measurable_KPR.stronglyMeasurable (measurable_csRJ _) GPR (fun _ => measurable_const)
    enorm_iteratedFDeriv_KPR_le_GPR lintegral_GPR_ne_top

theorem symReg_piece_RJ_P2 (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (tripleS R₁.m R₂.m KPRn (LsRJ R₁ R₂) (csRJ Unit)) :=
  tripleS_symReg (isBundle_LsRJ h₁ h₂) h₁.reg h₂.reg
    (fun _ => (contDiff_prod2 contDiff_phiR contDiff_chiInvRc).neg)
    measurable_KPRn.stronglyMeasurable (measurable_csRJ _) GPR (fun _ => measurable_const)
    (fun c x q => by rw [KPRn_iteratedFDeriv]; exact enorm_iteratedFDeriv_KPR_le_GPR c x q)
    lintegral_GPR_ne_top

/-- The bundle `ℓ₂ + εα₁` of the `χ₀` and second `χ_∞` pieces of `R J`. -/
@[expose] def yRJL (R₁ : RSym ι₁) : (ι₁ ⊕ ι₂) ⊕ Unit → ℤ := y3 R₁.y₂ 0 R₁.ε

/-- The bundle `ℓ₃` of the first `χ_∞` piece of `R J`. -/
@[expose] def yRJR (R₂ : JSym ι₂) : (ι₁ ⊕ ι₂) ⊕ Unit → ℤ := y3 0 R₂.y 0

theorem exists_piece_RJ_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSym ((ι₁ ⊕ ι₂) ⊕ Unit),
      S.Bound θ A (3 * (16 * (3 * N₁) * N₂ * (16 * (CkM * IM) * CPhi))) ∧ ∀ α t s,
      S.kernel α t s = ∫ z, tripleS R₁.m R₂.m KMR (LsRJ R₁ R₂) (csRJ (ℝ × ℝ)) α z *
        jker (bundle (yRJL (ι₂ := ι₂) R₁) α)
          ((eRJ (ℝ × ℝ) z).1.1 + (bMR (eRJ (ℝ × ℝ) z).2).1)
          ((eRJ (ℝ × ℝ) z).1.2 + (bMR (eRJ (ℝ × ℝ) z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * (CkM * IM) * CPhi := by
    have := kerM_bound.1; have := IM_nonneg; have := CPhi_nonneg; positivity
  obtain ⟨S, -, hS, hk⟩ := JSym.ofGenE
    (isBundle_y3 h₁.bundle₂ isBundle_zero (abs_sign_le h₁.sign)) (symReg_piece_RJ_M h₁ h₂)
    (eRJ (ℝ × ℝ)) (measurePreserving_eRJ _) measurable_bMR (by positivity)
    (norm_piece_RJ_M h0 h1 hA h₁ h₂)
  exact ⟨S, hS, hk⟩

theorem exists_piece_RJ_P1 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSym ((ι₁ ⊕ ι₂) ⊕ Unit),
      S.Bound θ A (3 * (16 * (6 * N₁) * (2 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))) ∧ ∀ α t s,
      S.kernel α t s = ∫ z, tripleS R₁.m R₂.m KPR (LsRJ R₁ R₂) (csRJ Unit) α z *
        jker (bundle (yRJR (ι₁ := ι₁) R₂) α)
          ((eRJ Unit z).1.1 + (bP1R (eRJ Unit z).2).1)
          ((eRJ Unit z).1.2 + (bP1R (eRJ Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  obtain ⟨S, -, hS, hk⟩ := JSym.ofGenE
    (isBundle_y3 isBundle_zero h₂.bundle (show |(0 : ℤ)| ≤ 1 by simp))
    (symReg_piece_RJ_P1 h₁ h₂)
    (eRJ Unit) (measurePreserving_eRJ _) measurable_bP1R (by positivity)
    (norm_piece_RJ_P1 h0 h1 hA h₁ h₂)
  exact ⟨S, hS, hk⟩

theorem exists_piece_RJ_P2 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSym ((ι₁ ⊕ ι₂) ⊕ Unit),
      S.Bound θ A (3 * (16 * (3 * N₁) * N₂ * (16 * Cθ θ * (CPhi * CPhi)))) ∧ ∀ α t s,
      S.kernel α t s = ∫ z, tripleS R₁.m R₂.m KPRn (LsRJ R₁ R₂) (csRJ Unit) α z *
        jker (bundle (yRJL (ι₂ := ι₂) R₁) α)
          ((eRJ Unit z).1.1 + (bP2R (eRJ Unit z).2).1)
          ((eRJ Unit z).1.2 + (bP2R (eRJ Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ 16 * Cθ θ * (CPhi * CPhi) := by
    have := Cθ_nonneg h0 h1; have := CPhi_nonneg; positivity
  obtain ⟨S, -, hS, hk⟩ := JSym.ofGenE
    (isBundle_y3 h₁.bundle₂ isBundle_zero (abs_sign_le h₁.sign)) (symReg_piece_RJ_P2 h₁ h₂)
    (eRJ Unit) (measurePreserving_eRJ _) measurable_bP2R (by positivity)
    (norm_piece_RJ_P2 h0 h1 hA h₁ h₂)
  exact ⟨S, hS, hk⟩

end Regular

end WaveTurbulence.ClassJR
